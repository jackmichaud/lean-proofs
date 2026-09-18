/-
Copyright (c) 2026 Jack Michaud. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Michaud
-/

import Leanproofs.Catalog
import Leanproofs.Tests.Support

/-!
# Normalized knowledge model tests

The canonical graph and its joined runtime view are tested together so information cannot
silently disappear across normalized-record lookups.
-/

open Lean Frontier

namespace Frontier.Test

def testKnowledgeModel (suite : Suite) : IO Unit := do
  let claimId : Knowledge.ClaimId := ⟨"normalized-fixture"⟩
  let formalizationId : Knowledge.FormalizationId := ⟨"normalized-fixture:primary"⟩
  let citationId : Knowledge.CitationId := ⟨"normalized-fixture:citation"⟩
  let registry : Knowledge.Registry := {
    claims := #[{
      id := claimId
      title := "Normalized fixture"
      summary := "Exercises the canonical projection."
      kind := .ordinary
      topic := "logic"
      tags := #["normalization", "fixture"]
      authors := #["Test Author"]
      source? := some "curatorial-note"
      created := "2026-01-02"
      updated := "2026-01-03"
    }]
    formalizations := #[{
      id := formalizationId
      claimId := claimId
      statement := `FermatFromScratch.pow_card
      status := .disproved
      baseTheory? := some { description := "A base theory" }
      authors := #["Formalizer"]
      tooling := #["Test Tool"]
    }]
    certificates := #[{
      id := ⟨"normalized-fixture:certificate"⟩
      formalizationId := formalizationId
      declaration := `FermatFromScratch.pow_card
      conclusion := .refutes
      method := .counterexample
      authors := #["Prover"]
    }]
    sanityChecks := #[{
      id := ⟨"normalized-fixture:sanity"⟩
      formalizationId := formalizationId
      declaration := `FermatFromScratch.pow_card
      role := .workedExample
    }]
    citations := #[{ id := citationId, display := "A traditional source." }]
    literatureAssertions := #[{
      id := ⟨"normalized-fixture:literature"⟩
      claimId := claimId
      conclusion := .folklore
      citations := #[citationId]
      observed := "2026-01-03"
    }]
  }
  check suite "canonical fixture is structurally valid" registry.validationErrors.isEmpty
  let entries := registry.entries
  check suite "canonical registry joins exactly one runtime entry" (entries.size == 1)
  match entries[0]? with
  | none => check suite "canonical runtime view contains its claim" false
  | some entry =>
      check suite "runtime view retains claim metadata"
        (entry.id == "normalized-fixture" && entry.title == "Normalized fixture" &&
          entry.claim.authors == #["Test Author"] &&
          entry.claim.source? == some "curatorial-note")
      check suite "runtime view retains formalization state"
        (entry.status == .disproved && entry.statement == `FermatFromScratch.pow_card &&
          entry.baseTheory? == some "A base theory" &&
          entry.formalization.tooling == #["Test Tool"])
      check suite "runtime view retains certificate semantics"
        (entry.certificate?.map (·.declaration) == some `FermatFromScratch.pow_card &&
          entry.certificate?.map (·.method) == some .counterexample)
      check suite "runtime view retains literature and sanity records"
        (entry.literature == .folklore && entry.citation? == some "A traditional source." &&
          entry.sanityChecks.map (·.declaration) == #[`FermatFromScratch.pow_card])
  check suite "committed normalized catalog is structurally valid"
    knowledgeCatalog.validationErrors.isEmpty
  check suite "runtime view covers every canonical claim"
    (knowledgeCatalog.entries.size == knowledgeCatalog.claims.size &&
      knowledgeCatalog.entries.map (·.id) == knowledgeCatalog.claims.map (·.id.value))
  check suite "open formalizations remain distinct from settled literature"
    ((knowledgeCatalog.findClaim? "catalan-conjecture" |>.map fun entry =>
      entry.status == .open && entry.literature == .affirmed &&
        entry.certificate?.isNone).getD false)
  let malformed := { registry with formalizations := #[] }
  check suite "validation rejects claims without a primary formalization"
    (malformed.validationErrors.any (·.contains "primary formalizations"))
  let dangling := { registry with
    certificates := #[{ registry.certificates[0]! with
      formalizationId := ⟨"missing-formalization"⟩ }] }
  check suite "validation rejects dangling artifact references"
    (dangling.validationErrors.any (·.contains "unknown formalization"))

end Frontier.Test
