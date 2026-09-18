/-
Copyright (c) 2026 Jack Michaud. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Michaud
-/

import Leanproofs.Tests.Support

/-!
# Batch proof evaluation tests

Kept callable independently until the shared runner adopts `testBatchProof`.
-/

open Lean Frontier Frontier.CLI

namespace Frontier.Test

private def result? (batch : ProofBatchResult) (id : String) : Option ProofActionResult :=
  batch.results.find? (·.actionId == id)

def testBatchProof (suite : Suite) (context : Context) : IO Unit := do
  let origin := ProofOrigin.proposition "∀ n : ℕ, n + 0 = n"
  let batch ← runProofBatch context origin #[
    { id := "introduce", tactic := "intro n" },
    { id := "reject", tactic := "exact nonsense_lemma" },
    { id := "finish", tactic := "simp" }
  ] defaultTacticHeartbeats

  check suite "a batch returns one correlated result per action"
    (batch.results.map (·.actionId) == #["introduce", "reject", "finish"])

  let some introduced := (result? batch "introduce" >>= (·.step?))
    | check suite "an accepted batch branch has a proof step" false
  check suite "a non-closing tactic is accepted"
    ((result? batch "introduce").map (·.outcome) == some .accepted)
  check suite "the accepted branch contains only its own tactic"
    (introduced.script.size == 1 && introduced.script[0]? == some "  intro n")
    s!"got {introduced.script}"

  let some rejected := (result? batch "reject" >>= (·.step?))
    | check suite "a rejected batch branch has a proof step" false
  check suite "a tactic diagnostic is classified as rejected"
    ((result? batch "reject").map (·.outcome) == some .rejected)
  check suite "a rejected branch does not retain its tactic"
    (rejected.script.isEmpty && !rejected.errors.isEmpty)
    s!"script {rejected.script}, errors {rejected.errors}"

  let some finished := (result? batch "finish" >>= (·.step?))
    | check suite "a completed batch branch has a proof step" false
  check suite "a closing tactic is classified as complete"
    ((result? batch "finish").map (·.outcome) == some .complete && finished.isComplete)
  check suite "sibling actions all start from the same parent"
    (finished.script.size == 1 && finished.script[0]? == some "  simp")
    s!"got {finished.script}"

  let policyBatch ← runProofBatch context (.proposition "(2 : ℕ) + 2 = 4") #[
    { id := "forbidden", tactic := "native_decide" },
    { id := "trusted", tactic := "decide" }
  ] defaultTacticHeartbeats
  let some forbidden := (result? policyBatch "forbidden" >>= (·.step?))
    | check suite "a policy-invalid branch has a proof step" false
  check suite "a forbidden axiom is classified as policy rejected"
    ((result? policyBatch "forbidden").map (·.outcome) == some .policyRejected
      && !forbidden.policyErrors.isEmpty)
  check suite "a policy-invalid action does not block a sibling"
    ((result? policyBatch "trusted").map (·.outcome) == some .complete)

end Frontier.Test
