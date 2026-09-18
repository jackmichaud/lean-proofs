/-
Copyright (c) 2026 Jack Michaud. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Michaud
-/

import Leanproofs.Tests.Support

/-!
# Proof and protocol tests
-/

open Lean Frontier Frontier.CLI

namespace Frontier.Test

/-! ## Argument and request parsing -/

def testParsing (suite : Suite) : IO Unit := do
  check suite "a flag is stripped from anywhere in the arguments"
    (takeFlag "--json" ["show", "--json", "x"] == (true, ["show", "x"]))
  check suite "an absent flag is reported absent"
    (takeFlag "--json" ["show", "x"] == (false, ["show", "x"]))
  check suite "an option value is read and removed"
    (takeOption "--limit" ["search", "q", "--limit", "5"] == (.value "5", ["search", "q"]))
  check suite "an option in the middle is read and removed"
    (takeOption "--limit" ["search", "--limit", "5", "q"] == (.value "5", ["search", "q"]))
  check suite "an absent option leaves the arguments alone"
    (takeOption "--limit" ["search", "q"] == (.absent, ["search", "q"]))
  -- A trailing flag used to report itself absent and stay in the positional arguments, where
  -- `search` folded it into the query and returned zero hits with a success exit code. A
  -- malformed request answered with a plausible empty result is the worst available outcome.
  check suite "a trailing option with no value is distinguished from an absent one"
    (takeOption "--limit" ["search", "--limit"] == (.valueless, ["search"]))
  check suite "a valueless option is an error, not a fallback"
    ((takeNat "--limit" 25 ["search", "--limit"]).toOption.isNone)
  check suite "a valueless string option is an error"
    ((takeString "--goal" ["suggest", "--goal"]).toOption.isNone)
  check suite "a string option value is read and removed"
    ((takeString "--goal" ["suggest", "--goal", "x"]).toOption == some (some "x", ["suggest"]))
  check suite "an absent string option is not an error"
    ((takeString "--goal" ["suggest", "x"]).toOption == some (none, ["suggest", "x"]))
  check suite "a numeric option parses"
    ((takeNat "--limit" 25 ["search", "--limit", "5"]).toOption == some (5, ["search"]))
  check suite "an absent numeric option falls back"
    ((takeNat "--limit" 25 ["search"]).toOption == some (25, ["search"]))
  check suite "a non-numeric option value is an error"
    ((takeNat "--limit" 25 ["search", "--limit", "many"]).toOption.isNone)

/-! ## Interactive proving

The claim `prove` makes is that a goal state it reports is the goal state Lean produces when
compiling the assembled script. Two things can break that, and both did while it was written:
a state carried between elaborator runs arrives subtly corrupted, and a proof term audited
against the wrong environment hides the axiom a tactic just introduced. Neither announces
itself, so both are pinned here. -/

def testProving (suite : Suite) (context : Context) : IO Unit := do
  let stepOf : Payload → Option ProofStep
    | .proof step => some step
    | _ => none
  let failed : Payload → Bool
    | .failure _ => true
    | _ => false
  -- Open a goal, apply blocks in order, and return the last step.
  let sequence (goal : String) (blocks : List String) : IO (Option ProofStep) := do
    let mut step? ← pure (stepOf (← compute context ["prove", "--goal", goal]))
    for block in blocks do
      let some step := step? | return none
      step? := stepOf (← compute context
        ["prove", "--state", toString step.id, "--tactic", block])
    return step?

  -- Opening a goal reports it rather than proving anything.
  let some opened := stepOf (← compute context ["prove", "--goal", "∀ n : ℕ, n + 0 = n"])
    | check suite "prove opens a goal" false
  check suite "an opened goal has one outstanding goal" (opened.goals.size == 1)
  check suite "an opened goal is not closed" (!opened.closed)
  check suite "an opened goal renders the proposition"
    (opened.goals.any (containsSubstring · "n + 0 = n")) s!"got {opened.goals}"

  -- A tactic advances the state, and the hypothesis it introduced shows up in the goal.
  let some introduced ← sequence "∀ n : ℕ, n + 0 = n" ["intro n"]
    | check suite "a tactic advances the state" false
  check suite "an introduced hypothesis appears in the goal"
    (introduced.goals.any (containsSubstring · "n : ℕ")) s!"got {introduced.goals}"

  let some finished ← sequence "∀ n : ℕ, n + 0 = n" ["intro n", "simp"]
    | check suite "a proof can be finished across steps" false
  check suite "a finished proof is closed" finished.closed
  check suite "a finished proof is complete" finished.isComplete
    s!"errors {finished.errors}, policy {finished.policyErrors}"
  check suite "a finished proof accumulates its script" (finished.script.size == 2)
  check suite "the scaffold carries the goal and the script"
    (containsSubstring finished.scaffold "theorem"
      && containsSubstring finished.scaffold "intro n"
      && containsSubstring finished.scaffold "simp")
    s!"got {finished.scaffold}"

  -- The regression that motivated replaying the script instead of resuming a saved elaborator
  -- state. Resuming one, `intro` succeeded and this `exact` then failed to synthesize an
  -- instance visible in its own printed goal, while the identical script compiled fine as a
  -- single block. A goal state that depends on how many requests it took to get there is
  -- worse than no goal state.
  let some acrossSteps ← sequence "∀ (p : ℕ) [Fact p.Prime] (a : ZMod p), a ^ p = a"
      ["intro p hp a", "exact ZMod.pow_card a"]
    | check suite "an instance-carrying goal survives being advanced in steps" false
  check suite "an instance-carrying goal survives being advanced in steps"
    acrossSteps.isComplete
    s!"errors {acrossSteps.errors}, policy {acrossSteps.policyErrors}"
  let some oneBlock ← sequence "∀ (p : ℕ) [Fact p.Prime] (a : ZMod p), a ^ p = a"
      ["intro p hp a\nexact ZMod.pow_card a"]
    | check suite "the same script in one block also completes" false
  check suite "stepwise and single-block runs of a script agree"
    (oneBlock.isComplete == acrossSteps.isComplete)

  -- `sorry` closes every goal. If `closed` were the reported verdict, this would read as a
  -- proof of anything.
  let some sorried ← sequence "(2:ℕ) + 2 = 5" ["sorry"]
    | check suite "a sorried goal reports" false
  check suite "`sorry` closes the goal" sorried.closed
  check suite "`sorry` is not a complete proof" (!sorried.isComplete)
  check suite "`sorry` is rejected by the axiom policy"
    (sorried.policyErrors.any (containsSubstring · "sorryAx")) s!"got {sorried.policyErrors}"

  -- The regression for auditing in the post-elaboration environment. `native_decide` emits a
  -- fresh axiom while it runs, so an audit against the environment as it was before the
  -- tactic finds nothing and calls the result clean.
  let some natively ← sequence "(2:ℕ) + 2 = 4" ["native_decide"]
    | check suite "a native_decide goal reports" false
  check suite "`native_decide` closes the goal" natively.closed
  check suite "`native_decide` is not a complete proof" (!natively.isComplete)
  check suite "`native_decide` is caught by the axiom policy"
    (!natively.policyErrors.isEmpty) s!"axioms {natively.axioms}"
  check suite "a tactic-emitted axiom is reported"
    (natively.axioms.any fun name => containsSubstring name.toString "native_decide")
    s!"got {natively.axioms}"
  -- The honest version of the same proposition has to still pass, or the check above is just
  -- rejecting arithmetic.
  let some decided ← sequence "(2:ℕ) + 2 = 4" ["decide"]
    | check suite "a decided goal reports" false
  check suite "`decide` is a complete proof" decided.isComplete
    s!"errors {decided.errors}, policy {decided.policyErrors}"

  -- An unknown identifier is logged rather than thrown, and elaborates to `sorry`.
  let some unknown ← sequence "(2:ℕ) + 2 = 4" ["exact nonsense_lemma"]
    | check suite "an unknown identifier reports" false
  check suite "an unknown identifier is an error, not a closed goal"
    (!unknown.closed && !unknown.errors.isEmpty) s!"errors {unknown.errors}"
  check suite "a tactic error is positioned in the caller's own block"
    (unknown.errors.any (containsSubstring · "1:6")) s!"got {unknown.errors}"

  -- A block that failed changed nothing, so it must not join the script the scaffold is
  -- built from, and the goals reported with the error are the ones still outstanding.
  let some based := stepOf (← compute context ["prove", "--goal", "∀ n : ℕ, n + 0 = n",
    "--tactic", "intro n"]) | check suite "the retry fixture opens" false
  let some rejected := stepOf (← compute context
    ["prove", "--state", toString based.id, "--tactic", "exact nonsense_lemma"])
    | check suite "a failing block reports" false
  check suite "a failing block is not added to the script"
    (rejected.script == based.script) s!"got {rejected.script}"
  check suite "a failing block still reports the outstanding goal"
    (rejected.goals.any (containsSubstring · "n + 0 = n")) s!"got {rejected.goals}"
  let some retried := stepOf (← compute context
    ["prove", "--state", toString rejected.id, "--tactic", "simp"])
    | check suite "a state can be retried after a failure" false
  check suite "a state is still usable after a failed tactic" retried.isComplete
    s!"errors {retried.errors}"

  check suite "prove rejects --goal and --state together"
    (failed (← compute context ["prove", "--goal", "True", "--state", "1"]))
  check suite "prove requires a goal or a state"
    (failed (← compute context ["prove", "--tactic", "simp"]))
  check suite "prove rejects an empty tactic block"
    (failed (← compute context ["prove", "--goal", "True", "--tactic", "   "]))
  check suite "prove rejects a non-numeric state"
    (failed (← compute context ["prove", "--state", "nope", "--tactic", "simp"]))
  check suite "prove reports an unknown state"
    (failed (← compute context ["prove", "--state", "999999", "--tactic", "simp"]))
  check suite "prove rejects a goal that is not a proposition"
    (failed (← compute context ["prove", "--goal", "42"]))
  check suite "prove rejects an unparseable tactic block"
    (failed (← compute context ["prove", "--goal", "True", "--tactic", "intro ("]))

/-! ## Dispatch

The failure mode these cover is not a crash but a plausible wrong answer: a malformed request
that comes back `ok` with an empty result reads, to an agent, as a fact about mathlib. -/

def testDispatch (suite : Suite) (context : Context) : IO Unit := do
  let failed : Payload → Bool
    | .failure _ => true
    | _ => false

  check suite "a valueless --limit is an error rather than an empty result"
    (failed (← compute context ["search", "pow_card", "--limit"]))
  check suite "a valueless --goal is an error"
    (failed (← compute context ["suggest", "--goal"]))
  check suite "a valueless --heartbeats is an error"
    (failed (← compute context ["check", "--heartbeats", "x.lean"]))
  check suite "an unknown command is an error"
    (failed (← compute context ["frobnicate"]))
  check suite "suggest rejects a goal and an id together"
    (failed (← compute context ["suggest", "fermat-units", "--goal", "True"]))
  check suite "serve cannot be nested inside a session"
    (failed (← compute context ["serve"]))

  -- Unbounded elaboration is acceptable for a one-shot command and not inside a session, where
  -- it would block every later request with no way to tell a hang from slow work.
  check suite "unbounded heartbeats are rejected inside a session"
    (failed (← compute { context with session := true }
      ["check", "--heartbeats", "0", "x.lean"]))
  check suite "unbounded heartbeats are allowed for a one-shot command"
    (match ← compute { context with session := false }
        ["check", "--heartbeats", "0", "definitely-absent.lean"] with
      -- Reaches the draft check and reports the missing file, rather than being refused.
      | .draft _ report _ _ => report.fatal.any (containsSubstring · "does not exist")
      | _ => false)


end Frontier.Test
