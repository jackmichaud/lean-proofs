/-
Copyright (c) 2026 Jack Michaud. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Michaud
-/

import Leanproofs.Frontier.Core

open Lean

namespace Frontier.CLI

/-! ## Elaborating a goal

Premise selection matters most for a proposition that is *not* in the catalog: an agent's goal
is something it just wrote. Ranking premises only for registered ids makes the feature
unavailable exactly when it is needed, so a goal has to be elaborable from a string. -/

/-- Default elaboration budget for a goal supplied on the command line, in heartbeats. -/
def defaultGoalHeartbeats : Nat := 200000

/-- Elaborate `source` as a term against the imported environment.

`withoutErrToSorry` is load-bearing. By default a failed elaboration *succeeds* and returns
`sorryAx`, which here would mean silently ranking premises against a proposition built out of
an error — plausible-looking output for the wrong goal. An error has to be an error. -/
def elabProposition (env : Environment) (source : String)
    (heartbeats : Nat := defaultGoalHeartbeats) : IO (Except String Expr) := do
  if source.trimAscii.isEmpty then
    return .error "the goal is empty"
  match Parser.runParserCategory env `term source "<goal>" with
  | .error message => return .error s!"could not parse the goal as a Lean term: {message}"
  | .ok stx =>
      try
        let expr ← runCoreM env (heartbeats := heartbeats) <| Meta.MetaM.run' <|
          Elab.Term.TermElabM.run' <| Elab.Term.withoutErrToSorry do
            let expr ← Elab.Term.elabTerm stx none
            Elab.Term.synthesizeSyntheticMVarsNoPostponing
            instantiateMVars expr
        if expr.hasSorry then
          return .error "the goal elaborated to `sorry` and is not a well-formed proposition"
        if expr.hasExprMVar then
          return .error
            "the goal has unresolved metavariables; annotate it so every implicit is determined"
        let isProposition ← runCoreM env (heartbeats := heartbeats) <|
          Meta.MetaM.run' (Meta.isProp expr)
        unless isProposition do
          return .error "the goal is a term but not a proposition"
        return .ok expr
      catch exception =>
        return .error exception.toString

/-! ## Proof state

`check` is a compile loop: hand it a file, it reports what Lean said. That is the wrong
granularity for *searching* for a proof. An agent that cannot ask "what is the goal after
`intro n`" or "does `simp` close this" has to guess a whole proof, compile it, and read an
error — so it iterates against a file when the thing it is exploring is a goal.
`docs/retrieval-and-agents.md` lists proof-state interaction as the capability gap above
premise retrieval for that reason.

`prove` closes it. A proposition opens a proof state, a tactic block advances it, and the
state persists across requests in a session so the prefix does not have to be resent.

## Why this is not a REPL subprocess

The roadmap recommended wrapping `leanprover-community/repl` rather than hand-rolling an
interaction layer, and for environment setup and goal serialization that argument is sound.
The deciding measurement is memory. This process already holds mathlib: about 5.7GB resident,
plus the premise index. A `repl` subprocess with its own `import Mathlib` would hold another
several gigabytes for a second copy of the same environment, and the whole design of
`frontier serve` is one long-lived process that imports once. So `prove` runs Lean's own
`Elab.Tactic` against the environment already loaded here — no second import, no second
environment, and tactics see exactly the declarations `check` and `suggest` do.

What that gives up is `repl`'s maintenance of the protocol surface across toolchain bumps.
The exposure is small and deliberate: the four entry points used below — `Elab.Tactic.run`,
`Elab.Tactic.setGoals`, `Elab.Term.saveState`, and `Meta.ppGoal` — are the stable core of that
API, not its edges.

## A closed goal is not a proved theorem

This is the trap, and it is not hypothetical: tactic elaboration reports an unknown identifier
as a *message* and returns `sorryAx`, so "no goals remain" is equally true of `exact
nonsense_lemma` and of `sorry`. Both were measured doing exactly that while this was being
built. Completeness therefore means all three of: no goals outstanding, no error logged, and an
assembled proof term that satisfies the axiom policy — the same standard `validate` holds a
certificate to. -/

/-- Default elaboration budget for a tactic block, in heartbeats. Matched to the draft budget:
a generated tactic that does not terminate is the ordinary failure mode, not an edge case. -/
def defaultTacticHeartbeats : Nat := 400000

/-- The caller's tactic block as the body of a synthesized `by`, with the column shift applied.

Relative indentation is load-bearing in Lean — nested `·` bullets and `induction … with`
alternatives are delimited by column — so this strips the block's *common* indentation and adds
a uniform two, rather than re-indenting each line to the same place and flattening the
structure. Because the shift is then identical on every line, a position Lean reports in this
source can be mapped back to the caller's own text by subtracting it; see `tacticMessage`.

Returns the body and that shift. -/
def tacticBlockBody (tactic : String) : String × Nat :=
  let lines := ((tactic.replace "\r\n" "\n").splitOn "\n").map fun line =>
    String.ofList (line.toList.reverse.dropWhile (· == ' ')).reverse
  let indentOf (line : String) : Nat := (line.toList.takeWhile (· == ' ')).length
  let indents := (lines.filter fun line => !line.trimAscii.isEmpty).map indentOf
  let common := indents.foldl (init := indents.headD 0) min
  let body := lines.map fun line =>
    if line.trimAscii.isEmpty then "" else "  " ++ line.drop common
  ("\n".intercalate body, common)

/-- Render a diagnostic with a position in the caller's tactic block rather than in the source
this module synthesized around it.

The synthesized source is `by`, a newline, then the block re-indented to column two. So a
reported line is one further down than the caller's, and a reported column is `2 - common`
further right. Passing Lean's own coordinates through would point an agent at a position in a
string it never saw. -/
def tacticMessage (lineOffset shift : Nat) (message : Message) : IO String := do
  let text ← message.data.toString
  let severity := match message.severity with
    | .error => "error"
    | .warning => "warning"
    | .information => "info"
  let raw := message.pos.column + shift
  let column := if raw ≥ 2 then raw - 2 else 0
  -- A position at or above the caller's block is in the replayed prefix, which they did not
  -- send this time. Reporting it as line zero of their input would be a lie, so leave the
  -- assembled coordinates alone and say which script they belong to.
  if message.pos.line ≤ lineOffset then
    return s!"in the replayed script at line {message.pos.line - 1}: {severity}: {text}"
  return s!"{message.pos.line - lineOffset}:{column}: {severity}: {text}"

/-- One `prove` step's report. -/
structure ProofStep where
  /-- The state to pass to the next `prove --state`. -/
  id : Nat
  /-- Outstanding goals, pretty-printed with their hypotheses. -/
  goals : Array String
  /-- No goals outstanding. Necessary for a proof and, on its own, not remotely sufficient —
  see the section docstring. -/
  closed : Bool
  errors : Array String
  /-- Axioms the assembled proof term rests on, once there is one. -/
  axioms : Array Name
  policyErrors : Array String
  /-- Normalized tactic blocks applied so far. -/
  script : Array String
  /-- A draft `theorem` for the script so far: the bridge from an interactive attempt back to a
  file that `check` and then the registry can audit. -/
  scaffold : String

/-- Whether the attempt is a proof: closed, quiet, and within the axiom policy. -/
def ProofStep.isComplete (step : ProofStep) : Bool :=
  step.closed && step.errors.isEmpty && step.policyErrors.isEmpty

/-- Where a step starts.

The proposition is carried as *source*, not as an elaborated `Expr`, and that is load-bearing
rather than incidental — see the note in `runProofStep`. -/
inductive ProofOrigin where
  | proposition (goalSource : String)
  | resume (state : ProofState)

/-- A draft `theorem` for `script`, ready to paste into a file and `check`.

`sorry` stands in for an empty script so that the scaffold is always a syntactically complete
declaration — one that `check` will reject for exactly the right reason. -/
def proofScaffold (goalSource : String) (script : Array String) : String :=
  let proposition := " ".intercalate <|
    (goalSource.splitOn "\n").filterMap fun line =>
      let trimmed := line.trimAscii.toString
      if trimmed.isEmpty then none else some trimmed
  let body := if script.isEmpty then "  sorry" else "\n".intercalate script.toList
  s!"theorem frontier_attempt : {proposition} := by\n{body}"

/-- What one replay produced, before the axiom audit. -/
private structure ScriptRun where
  /-- Outstanding goals, pretty-printed with their hypotheses. -/
  rendered : Array String
  errors : Array String
  /-- The assembled proof term, when nothing was left and nothing complained. -/
  proof? : Option Expr
  /-- The environment *after* elaboration, which is the only one the proof term can be audited
  against. A tactic may add declarations: `native_decide` emits a fresh per-invocation axiom
  and proves the goal with it, so auditing against the environment as it was before the
  tactic ran finds no axioms at all and reports the result as clean. That is the exact
  soundness hole the axiom policy exists to close, and it was open here until measured. -/
  env : Environment

/-- Store a state and hand back its id, dropping the oldest once the window is full. -/
def Context.storeProofState (context : Context) (state : ProofState) : IO Nat := do
  let (states, id) ← context.proofStatesRef.get
  let states := states.insert id state
  let states :=
    if id ≥ retainedProofStates then states.erase (id - retainedProofStates) else states
  context.proofStatesRef.set (states, id + 1)
  return id

/-- Look up a state, distinguishing the three ways it can be absent: dropped from the window,
never created, or asked for outside a session where none can exist. -/
def Context.proofState? (context : Context) (id : Nat) : IO (Except String ProofState) := do
  let (states, next) ← context.proofStatesRef.get
  if let some state := states[id]? then
    return .ok state
  if 0 < id && id < next then
    return .error s!"proof state {id} has been dropped; a session keeps the most recent \
      {retainedProofStates}"
  if !context.session then
    return .error s!"no proof state {id}; state ids exist only within a `frontier serve` \
      session, so a one-shot `prove --state` can never find one — pass `--goal` and `--tactic` \
      together, or open a session"
  return .error s!"no proof state {id}"

/-- Elaborate `goalSource` and run `script` against it, in one elaborator run.

`lineOffset` is the line in the assembled block that the caller's own text starts at, so
diagnostics can be reported against what they wrote. -/
def runScript (context : Context) (goalSource : String) (script : Array String)
    (lineOffset shift heartbeats : Nat) : IO (Except String ScriptRun) := do
  let env := context.env
  -- Parse before elaborating anything: a syntax error is the most useful thing to report and
  -- costs nothing to find.
  if goalSource.trimAscii.isEmpty then
    return .error "the goal is empty"
  let goalStx ←
    match Parser.runParserCategory env `term goalSource "<goal>" with
    | .error message => return .error s!"could not parse the goal as a Lean term: {message}"
    | .ok stx => pure stx
  let source := "by\n" ++ "\n".intercalate script.toList
  let block? ←
    if script.isEmpty then pure none
    else
      match Parser.runParserCategory env `term source "<tactic>" with
      | .error message => return .error s!"could not parse the tactic block: {message}"
      | .ok stx => pure (some stx)
  let run : CoreM (Except String ScriptRun) := Meta.MetaM.run' <| Elab.Term.TermElabM.run' do
    -- The goal is elaborated *here*, in the run that will host the tactics, for the same
    -- reason the whole script is replayed here: see `runProofStep`.
    let root? : Except String MVarId ←
      try
        Elab.Term.withoutErrToSorry do
          let goalType ← Elab.Term.elabTerm goalStx none
          Elab.Term.synthesizeSyntheticMVarsNoPostponing
          let goalType ← instantiateMVars goalType
          if goalType.hasSorry then
            return .error "the goal elaborated to `sorry` and is not a well-formed proposition"
          if goalType.hasExprMVar then
            return .error
              "the goal has unresolved metavariables; annotate it so every implicit is \
               determined"
          unless ← Meta.isProp goalType do
            return .error "the goal is a term but not a proposition"
          return .ok (← Meta.mkFreshExprMVar goalType).mvarId!
      catch exception =>
        return .error (← exception.toMessageData.toString)
    let root ←
      match root? with
      | .error message => return .error message
      | .ok root => pure root
    let mut errors : Array String := #[]
    let mut remaining := [root]
    if let some stx := block? then
      -- Only this request's diagnostics. The ambient log belongs to the session, and folding
      -- it in would re-report every earlier failure on every later request.
      let outer ← Core.getMessageLog
      Core.setMessageLog {}
      try
        remaining ← Elab.Tactic.run root (Elab.Tactic.evalTactic stx[1])
      catch exception =>
        errors := errors.push (← exception.toMessageData.toString)
      for message in (← Core.getMessageLog).toArray do
        if message.severity == .error then
          errors := errors.push (← tacticMessage lineOffset shift message)
      Core.setMessageLog outer
    let rendered ← remaining.toArray.mapM fun goal => do
      return (← Meta.ppGoal goal).pretty
    let proof? ←
      if remaining.isEmpty && errors.isEmpty then
        some <$> instantiateMVars (.mvar root)
      else
        pure none
    return .ok { rendered, errors, proof?, env := ← getEnv }
  runCoreM env (heartbeats := heartbeats) (fileName := "<tactic>") (source := some source) run

/-- Open or advance a proof attempt.

## Why the script is replayed rather than a state resumed

The obvious design is to suspend the elaborator — save `Elab.Term.SavedState` with the
outstanding goals, restore it on the next request, apply one more tactic. It was built that
way first, and it is wrong in a way that does not announce itself.

An elaborator state does not travel between runs intact. Hygienic binder names are minted from
a macro-scope counter in `Core.State`, so an elaborated `∀ (p : ℕ) [Fact p.Prime] …` carries
names like `inst._@._hyg.7` whose scope means nothing in a later run; the name generator, the
instance caches, and the metavariable context all have the same property. What that produced,
measured: `intro p hp a` succeeded, and the very next `exact ZMod.pow_card a` failed to
synthesize `Fact (Nat.Prime ⋯)` — an instance sitting in the printed goal. The identical script
compiled without complaint as a single `by` block. Silently wrong goal states are the one
failure a proof assistant must not have, and chasing which fields survive a boundary is a
losing game against a toolchain that is free to add more.

So a state here is just the proposition and the tactic script accepted so far, and every
request re-elaborates from the proposition in a single run. The agent still gets the
interactive loop without resending its prefix, because the prefix is kept for it.

The cost is re-running the prefix each step, bounded by `--heartbeats` like any other
elaboration. What it buys is worth more than the time: a goal state `prove` reports is by
construction the goal state Lean produces when compiling the assembled proof, so what an agent
explores and what `check` will later say cannot drift apart.

A block that fails is not added to the script, so the stored script always elaborates. -/
def runProofStep (context : Context) (origin : ProofOrigin) (tactic? : Option String)
    (heartbeats : Nat) : IO (Except String ProofStep) := do
  let (goalSource, prefixScript) :=
    match origin with
    | .proposition goalSource => (goalSource, #[])
    | .resume state => (state.goalSource, state.script)
  -- Normalize the new block, and work out where it lands in the assembled script so its
  -- diagnostics can be reported against the caller's own coordinates.
  let added? : Option (String × Nat) ←
    match tactic? with
    | none => pure none
    | some tactic =>
        if tactic.trimAscii.isEmpty then
          return .error "the tactic block is empty"
        pure (some (tacticBlockBody tactic))
  let prefixLines := prefixScript.foldl (init := 0) fun total body =>
    total + (body.splitOn "\n").length
  let (candidate, lineOffset, shift) :=
    match added? with
    | some (body, common) => (prefixScript.push body, 1 + prefixLines, common)
    | none => (prefixScript, 1, 0)
  let attempt ← runScript context goalSource candidate lineOffset shift heartbeats
  match attempt with
  | .error message => return .error message
  | .ok result =>
      -- A block that errored changed nothing, so it is neither stored nor counted in the
      -- script. Re-running the accepted prefix is what produces the goals to report with the
      -- error: they are the goals the caller still has to address.
      let (accepted, report) ←
        if result.errors.isEmpty || added?.isNone then
          pure (candidate, result)
        else
          match ← runScript context goalSource prefixScript 1 0 heartbeats with
          | .error message => return .error message
          | .ok baseline =>
              pure (prefixScript, { baseline with errors := result.errors })
      let mut axioms : NameSet := {}
      if let some proof := report.proof? then
        -- Audited in the post-elaboration environment, and against the same `reach` the
        -- registry audit uses, so a tactic-emitted axiom is found by the same code that gates
        -- a catalog certificate.
        let audited := { context with env := report.env }
        let mut cache : ReachCache := {}
        for constant in proof.getUsedConstants do
          let (reached, next) ← (reach audited constant).run cache
          cache := next
          axioms := reached.axioms.toArray.foldl (init := axioms) NameSet.insert
      let axiomArray := axioms.toArray.qsort Name.lt
      let id ← context.storeProofState { goalSource, script := accepted }
      return .ok {
        id
        goals := report.rendered
        closed := report.rendered.isEmpty && report.errors.isEmpty
        errors := report.errors
        axioms := axiomArray
        policyErrors :=
          if report.proof?.isSome then axiomPolicyErrors "the proof term" axiomArray else #[]
        script := accepted
        scaffold := proofScaffold goalSource accepted
      }


end Frontier.CLI
