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

`baseEntry` is deliberately *valid*. Every negative fixture below is that entry with exactly
one field broken, so a failing assertion names the check that stopped working rather than
leaving the cause to be guessed at. -/

def baseEntry : Entry := {
  id := "fixture"
  title := "Fixture"
  summary := "A valid fixture entry."
  status := .proved
  literature := .proved
  citation? := some "Fixture citation."
  topic := "number-theory"
  statement := `FermatFromScratch.pow_card
  certificate? := some `FermatFromScratch.pow_card
  evidence? := some .proof
  authors := #["Test Author"]
  created := "2026-01-01"
  updated := "2026-01-01"
}

def audit (context : Context) (entry : Entry) : IO Audit := do
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

