/-
Copyright (c) 2026 Jack Michaud. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Michaud
-/

import Leanproofs.Catalog
import Leanproofs.Tests.Support

/-!
# Normalized knowledge model tests

The canonical graph and its temporary audit projection are tested together so information
cannot silently disappear at the boundary.
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
  let projected := registry.toEntries
  check suite "canonical claim projects exactly one audit entry" (projected.size == 1)
  match projected[0]? with
  | none => check suite "canonical projection contains its claim" false
  | some entry =>
      check suite "projection preserves claim metadata"
        (entry.id == "normalized-fixture" && entry.title == "Normalized fixture" &&
          entry.authors == #["Test Author"] && entry.source? == some "curatorial-note")
      check suite "projection preserves formalization state"
        (entry.status == .disproved && entry.statement == `FermatFromScratch.pow_card &&
          entry.baseTheory? == some "A base theory" && entry.tooling == #["Test Tool"])
      check suite "projection preserves certificate semantics"
        (entry.certificate? == some `FermatFromScratch.pow_card &&
          entry.evidence? == some .counterexample)
      check suite "projection preserves literature and sanity records"
        (entry.literature == .folklore && entry.citation? == some "A traditional source." &&
          entry.sanityChecks == #[`FermatFromScratch.pow_card])
  check suite "committed normalized catalog is structurally valid"
    knowledgeCatalog.validationErrors.isEmpty
  check suite "legacy audit catalog is only a complete projection"
    (catalog.size == knowledgeCatalog.claims.size &&
      catalog.map (·.id) == knowledgeCatalog.claims.map (·.id.value))
  check suite "open formalizations remain distinct from settled literature"
    ((catalog.find? (·.id == "catalan-conjecture") |>.map fun entry =>
      entry.status == .open && entry.literature == .proved && entry.certificate?.isNone).getD false)
  let malformed := { registry with formalizations := #[] }
  check suite "validation rejects claims without a primary formalization"
    (malformed.validationErrors.any (·.contains "primary formalizations"))
  let dangling := { registry with
    certificates := #[{ registry.certificates[0]! with
      formalizationId := ⟨"missing-formalization"⟩ }] }
  check suite "validation rejects dangling artifact references"
    (dangling.validationErrors.any (·.contains "unknown formalization"))

end Frontier.Test
