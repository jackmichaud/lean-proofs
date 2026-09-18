/-
Copyright (c) 2026 Jack Michaud. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Michaud
-/

import Lean
import Leanproofs.Registry
import Leanproofs.Journal
import Leanproofs.Frontier.Fingerprint

/-!
# Frontier CLI

Audits the research catalog against a compiled Lean environment, searches all imported Lean
declarations, records work in progress, and exports a reusable machine-readable theorem index.

This module deliberately does *not* import `Leanproofs.Catalog`. The executable has to import
the project environment at runtime with initializers enabled, and re-initializing modules that
are also statically linked into the binary crashes the process. `Leanproofs.Main` therefore
links only `Lean` and this module, imports the project, and hands the catalog in as data. See
that module for the full explanation.
-/

open Lean

namespace Frontier.CLI

open Knowledge

/-! ## Axiom policy

The kernel reports which axioms a proof rests on. Frontier turns that report into a decision.
Anything outside the allowlist is a validation failure, not a footnote, because the roadmap
accepts Lean from automated agents and an unnoticed `native_decide` is a soundness hole. -/

/-- Axioms Frontier accepts. These are the three assumptions of ordinary classical
mathematics as formalized in mathlib. -/
def allowedAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

/-- Axioms that are always rejected, with the reason reported to the author. -/
def deniedAxioms : Array (Name × String) := #[
  (``sorryAx, "the proof is incomplete"),
  (`Lean.ofReduceBool,
    "`native_decide` trusts the Lean compiler and the runtime, which are outside the kernel"),
  (`Lean.ofReduceNat,
    "`native_decide` trusts the Lean compiler and the runtime, which are outside the kernel"),
  (`Lean.trustCompiler, "trusting the compiler places the compiler inside the trust base")
]

def allowedAxiomSet : NameSet :=
  allowedAxioms.foldl (init := {}) NameSet.insert

def policyFingerprintMaterial : String :=
  "frontier-axiom-policy/v1\nallow=" ++
    ",".intercalate (allowedAxioms.map Name.toString).toList ++ "\ndeny=" ++
    ",".intercalate (deniedAxioms.map (fun value => value.1.toString ++ ":" ++ value.2)).toList

/-- Why `name` is rejected, if it is.

`native_decide` does not always surface as `Lean.ofReduceBool`: current Lean emits a fresh
per-declaration axiom such as `Foo._native.native_decide.ax_1_1`. The allowlist catches those
either way — which is the reason this is an allowlist and not a denylist — but matching the
shape lets the error say *why* instead of leaving the author to work it out. -/
def deniedAxiomReason? (name : Name) : Option String :=
  match deniedAxioms.find? (·.1 == name) with
  | some (_, reason) => some reason
  | none =>
      let text := name.toString
      if (text.splitOn "native_decide").length > 1 then
        some "`native_decide` trusts the Lean compiler and the runtime, which are outside \
              the kernel; replace it with `decide` or a proof"
      else
        none

/-- Report every policy violation in `axioms`, attributing them to `role`. -/
def axiomPolicyErrors (role : String) (axioms : Array Name) : Array String := Id.run do
  let mut errors := #[]
  for name in axioms do
    if let some reason := deniedAxiomReason? name then
      errors := errors.push s!"{role} depends on the forbidden axiom '{name}': {reason}"
    else if !allowedAxiomSet.contains name then
      errors := errors.push
        s!"{role} depends on '{name}', which is not in the Frontier axiom allowlist \
           ({", ".intercalate (allowedAxioms.map Name.toString).toList}); \
           extend the policy deliberately if this assumption is intended"
  return errors

/-! ## Context -/

/-! ### The premise corpus

Ranking premises reads the constants out of every imported theorem's type. Over all of mathlib
that is a traversal of a few hundred thousand `Expr`s — seconds of work, affordable once and
not once per request, since an agent iterating on a proof calls `suggest` repeatedly. So the
extracted form is kept rather than the expressions: sorted constant arrays, over which overlap
is a merge instead of a set rebuilt per query. Defined here because `Context` memoizes it.

The trade is memory for latency, and it is deliberate: roughly 600MB of index on top of the
several gigabytes the imported environment already costs, against `suggest` dropping from
seconds per call to a fraction of one. A tool an agent calls once per proof attempt has to
answer at interactive speed. -/

/-- One imported theorem, reduced to what premise ranking reads. -/
structure Premise where
  name : Name
  /-- Constants in the statement, in `NameSet.toArray` order. -/
  constants : Array Name
  /-- Constants in the conclusion, in the same order. See `conclusionKeys`. -/
  keys : Array Name
  /-- Total IDF mass of `constants`: how much the statement carries in total, and the
  normalizer that keeps a sprawling theorem from outranking a focused one. -/
  mass : Float
  deriving Inhabited

/-- Every imported theorem prepared for ranking, with the corpus statistics whose weighting its
scores depend on. -/
structure PremiseIndex where
  premises : Array Premise
  frequency : Std.HashMap Name Nat
  documents : Nat

/-! ### Proof state

An attempt in progress, held between requests so an agent can advance one tactic at a time
without resending its prefix. See the `## Proof state` section for what `prove` does with
these; they are declared here because `Context` holds them. -/

/-- An attempt in progress: the proposition and the tactic script accepted so far.

Deliberately *not* a suspended elaborator state. See `runProofStep`. -/
structure ProofState where
  /-- The proposition as the caller wrote it. -/
  goalSource : String
  /-- Normalized tactic blocks applied so far, oldest first. Always a script that elaborates
  without error: a block that fails is reported and discarded rather than stored, so the
  scaffold is never a script that does not run. -/
  script : Array String

/-- How many proof states a session keeps. A state is two strings, so this is generous; ids are
sequential, so the oldest is the one to drop. -/
def retainedProofStates : Nat := 256

/-- Everything a command needs: the imported environment, the catalog loaded from it, and an
index from registered declaration names back to catalog ids. -/
structure Context where
  env : Environment
  catalog : Knowledge.Registry
  fingerprint : Fingerprint.Result
  registered : Std.HashMap Name String
  /-- Memoized premise corpus. Building it folds over the type of every imported theorem,
  which is affordable once and far too expensive to redo for each request in
  `frontier serve`. -/
  premiseIndexRef : IO.Ref (Option PremiseIndex)
  /-- Live proof attempts and the id to allocate next. Only useful inside a `frontier serve`
  session: a one-shot command exits before a second request could name one, which is why
  `Context.proofState?` says so rather than reporting a bare miss. -/
  proofStatesRef : IO.Ref (Std.HashMap Nat ProofState × Nat)
  /-- Attempt-scoped durable state ids mapped to the session-local replay states that implement
  them. Typed research operations never expose the numeric ids in `proofStatesRef`. -/
  researchProofStatesRef : IO.Ref (Std.HashMap String Nat)
  /-- Where the work journal lives. See `Leanproofs/Journal.lean`; it is untrusted data and
  never participates in an audit. -/
  workRoot : System.FilePath
  /-- Where journal mutations republish the aggregate the web workspace reads. `none` disables
  publishing, which is what the tests use. -/
  workPublish? : Option System.FilePath
  /-- Whether this is a long-lived `frontier serve` session. A few limits are stricter inside
  one, because a single request can otherwise degrade every later request. -/
  session : Bool := false

def Context.of (env : Environment) (catalog : Knowledge.Registry)
    (workRoot : System.FilePath) (workPublish? : Option System.FilePath) : IO Context := do
  let fingerprint ← Fingerprint.capture env {
    catalog := Fingerprint.catalogMaterial catalog
    policy := policyFingerprintMaterial
  }
  return {
    env, catalog, fingerprint, workRoot, workPublish?
    registered := catalog.formalizations.foldl (init := {}) fun map formalization =>
      match catalog.claims.find? (·.id == formalization.claimId) with
      | some claim =>
          let map := map.insert formalization.statement claim.id.value
          catalog.certificates.foldl (init := map) fun map certificate =>
            if certificate.formalizationId == formalization.id then
              map.insert certificate.declaration claim.id.value
            else map
      | none => map
    premiseIndexRef := ← IO.mkRef none
    -- Ids start at one: `prove --state 0` reads as a mistake, and it is useful for that to be
    -- reported as one rather than resolving to the first attempt of the session.
    proofStatesRef := ← IO.mkRef ({}, 1)
    researchProofStatesRef := ← IO.mkRef {} }

/-- The default context: journal at `FRONTIER_WORK_DIR` or `work/`, publishing to the path the
web workspace fetches. -/
def Context.default (env : Environment) (catalog : Knowledge.Registry) : IO Context := do
  Context.of env catalog (← Journal.defaultRoot) (some Journal.defaultExportPath)

def Context.find? (context : Context) (name : Name) : Option ConstantInfo :=
  context.env.find? name

def Context.entry? (context : Context) (id : String) : Option Knowledge.RegisteredClaim :=
  context.catalog.findClaim? id

/-! ## Environment traversal -/

/-- Every constant referenced by the type or the value of `name`. -/
def usedConstants (env : Environment) (name : Name) : Array Name :=
  match env.find? name with
  | none => #[]
  | some info =>
      let fromType := info.type.getUsedConstants
      match info.value? (allowOpaque := true) with
      | some value => fromType ++ value.getUsedConstants
      | none => fromType

/-- What one declaration transitively reaches: the axioms it rests on, and the *nearest*
catalog entries above it.

The catalog component stops descending at a registered declaration, so an entry's
dependencies are its minimal catalog ancestors rather than every ancestor. Traversal itself
does not stop, because axioms must still be audited through registered intermediates. -/
structure Reach where
  axioms : NameSet := {}
  catalog : Std.HashSet String := {}
  deriving Inhabited

def Reach.mergeAxioms (target source : Reach) : Reach :=
  { target with
    axioms := source.axioms.toArray.foldl (init := target.axioms) NameSet.insert }

abbrev ReachCache := Std.HashMap Name Reach

/-- Transitive axioms and minimal catalog ancestors of `root`.

The inner traversal is an explicit worklist rather than recursion: mathlib dependency chains
run thousands deep and a recursive walk overflows the stack.

Results are cached, and the walk reuses the cached result of any *registered* declaration it
reaches instead of descending through it again. Registered declarations form a DAG — Lean
forbids circular proofs — so the outer recursion terminates, and a catalog of n entries costs
one walk per entry rather than re-walking every ancestor entry's proof. `visiting` guards the
recursion anyway, so a malformed environment degrades rather than hangs. -/
partial def reachCore (context : Context) (root : Name) (visiting : NameSet) :
    StateM ReachCache Reach := do
  if let some cached := (← get)[root]? then
    return cached
  if visiting.contains root then
    return {}
  let visiting := visiting.insert root
  let mut result : Reach := {}
  if let some (.axiomInfo value) := context.find? root then
    result := { result with axioms := result.axioms.insert value.name }
  let mut seen : NameSet := NameSet.insert {} root
  let mut worklist : Array Name := usedConstants context.env root
  while !worklist.isEmpty do
    let name := worklist.back!
    worklist := worklist.pop
    if seen.contains name then
      continue
    seen := seen.insert name
    match context.registered[name]? with
    | some id =>
        -- Stop the catalog component here: `id` is a minimal registered ancestor. Keep
        -- merging axioms, which must be audited through registered intermediates.
        let sub ← reachCore context name visiting
        let merged := result.mergeAxioms sub
        result := { merged with catalog := merged.catalog.insert id }
    | none =>
        if let some info := context.find? name then
          if let .axiomInfo value := info then
            result := { result with axioms := result.axioms.insert value.name }
          worklist := worklist ++ usedConstants context.env name
  modify (·.insert root result)
  return result

/-- Transitive axioms and minimal catalog ancestors of `root`, threading the shared cache
through whichever monad the caller is working in. -/
def reach {m : Type → Type} [Monad m] (context : Context) (root : Name) :
    StateT ReachCache m Reach := do
  let (result, cache) := (reachCore context root {}).run (← get)
  set cache
  return result

def Reach.axiomArray (reach : Reach) : Array Name :=
  reach.axioms.toArray.qsort Name.lt

def Reach.catalogArray (reach : Reach) (selfId : String) : Array String :=
  (reach.catalog.toList.filter (· != selfId)).toArray.qsort (· < ·)

/-! ## Rendering -/

def declarationKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

/-- The proposition a declaration denotes.

For a theorem or axiom that is its type. For a `def _ : Prop := …` — how open conjectures are
registered — it is the *body*, since the type is just `Prop` and carries no mathematics. -/
def statementExpr? (info : ConstantInfo) : Option Expr :=
  match info with
  | .defnInfo value =>
      if value.type == .sort .zero then some value.value else none
  | .opaqueInfo value =>
      if value.type == .sort .zero then some value.value else none
  | .thmInfo value => some value.type
  | .axiomInfo value => some value.type
  | _ => none

def ppOptions : Options :=
  ({} : Options).setBool `pp.unicode.fun true

/-- Run a `CoreM` action against the imported environment.

`heartbeats` is `0` — unbounded — for rendering, which is our own code over declarations the
kernel already accepted. Anything that elaborates *input* must pass a finite budget: see
`elabProposition` and `checkDraft`.

`source` is the text positions in logged messages are relative to. The default empty file map
resolves every position to the start of the file, which is correct for actions that log
nothing and useless for anything that does — see `runProofStep`, which passes the tactic block
it synthesized so Lean's diagnostics can be mapped back onto what the caller wrote. -/
def runCoreM {α : Type} (env : Environment) (x : CoreM α) (heartbeats : Nat := 0)
    (fileName : String := "<frontier>") (source : Option String := none) : IO α := do
  let (result, _) ← x.toIO
    { fileName, options := ppOptions, maxHeartbeats := heartbeats
      fileMap := match source with
        | some text => text.toFileMap
        | none => default }
    { env := env }
  return result

/-- Pretty-print with mathlib notation.

This produces `↑a ^ p = ↑a` rather than `Eq (HPow.hPow …) …` only because `Leanproofs.Main`
imports the environment with `loadExts := true`; without it the delaborators registered by
`notation` are never loaded and every rendered type in the export is unreadable. -/
def prettyExpr (env : Environment) (e : Expr) : IO String := do
  let rendered ← runCoreM env (Meta.MetaM.run' (PrettyPrinter.ppExpr e))
  return Format.pretty rendered 98

def prettyType (env : Environment) (info : ConstantInfo) : IO String :=
  prettyExpr env info.type

/-- Render the proposition a statement declaration denotes, falling back to its type. -/
def prettyStatement (env : Environment) (info : ConstantInfo) : IO String :=
  match statementExpr? info with
  | some proposition => prettyExpr env proposition
  | none => prettyType env info


end Frontier.CLI
