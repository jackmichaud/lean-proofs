/-
Copyright (c) 2026 Jack Michaud. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Michaud
-/

import Leanproofs.CLI

/-!
# Frontier test support
-/

open Lean Frontier Frontier.CLI

namespace Frontier.Test

/-! ## Harness -/

structure Results where
  passed : Nat := 0
  failures : Array String := #[]

abbrev Suite := IO.Ref Results

def check (suite : Suite) (name : String) (condition : Bool) (detail : String := "") :
    IO Unit := do
  if condition then
    suite.modify fun results => { results with passed := results.passed + 1 }
  else
    suite.modify fun results =>
      { results with
        failures := results.failures.push
          (if detail.isEmpty then name else s!"{name}\n      {detail}") }

/-- Assert that `audit` reported an error mentioning `fragment`. -/
def expectError (suite : Suite) (name : String) (audit : Audit) (fragment : String) : IO Unit :=
  check suite name (audit.errors.any (containsSubstring · fragment))
    s!"expected an error containing '{fragment}', got {audit.errors}"

def expectValid (suite : Suite) (name : String) (audit : Audit) : IO Unit :=
  check suite name audit.isValid s!"expected no errors, got {audit.errors}"

/-! ## Fixtures

`baseRegistry` is deliberately *valid*. Every negative fixture below changes one normalized
record, so a failing assertion names the check that stopped working rather than
leaving the cause to be guessed at. -/

open Knowledge

def baseClaim : Claim := {
  id := ⟨"fixture"⟩, title := "Fixture", summary := "A valid fixture entry."
  topic := "number-theory", authors := #["Test Author"]
  created := "2026-01-01", updated := "2026-01-01"
}

def baseFormalization : Formalization := {
  id := ⟨"fixture:formalization:primary"⟩, claimId := baseClaim.id
  statement := `FermatFromScratch.pow_card, status := .proved
  authors := #["Test Author"]
}

def baseCertificate : Certificate := {
  id := ⟨"fixture:certificate"⟩, formalizationId := baseFormalization.id
  declaration := `FermatFromScratch.pow_card, conclusion := .affirms
  method := .directProof, authors := #["Test Author"]
}

def baseCitation : Citation := { id := ⟨"fixture:citation"⟩, display := "Fixture citation." }

def baseLiterature : LiteratureAssertion := {
  id := ⟨"fixture:literature"⟩, claimId := baseClaim.id, conclusion := .affirmed
  citations := #[baseCitation.id], observed := "2026-01-01"
}

def baseRegistry : Registry := {
  claims := #[baseClaim]
  formalizations := #[baseFormalization]
  certificates := #[baseCertificate]
  citations := #[baseCitation]
  literatureAssertions := #[baseLiterature]
}

def baseEntry : RegisteredClaim := baseRegistry.entries[0]!

def audit (context : Context) (entry : RegisteredClaim) : IO Audit := do
  let (result, _) ← (auditEntry context entry).run {}
  return result


/-! ## Draft fixtures -/

def withDraft {α : Type} (contents : String) (action : System.FilePath → IO α) : IO α := do
  let directory : System.FilePath := "build" / "test-drafts"
  IO.FS.createDirAll directory
  let path := directory / s!"draft-{hash contents}.lean"
  IO.FS.writeFile path contents
  try action path finally IO.FS.removeFile path

end Frontier.Test
