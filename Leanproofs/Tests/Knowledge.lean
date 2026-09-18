/-
Copyright (c) 2026 Jack Michaud. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Michaud
-/

import Leanproofs.Knowledge.LegacyAdapter
import Leanproofs.Tests.Support

/-!
# Normalized knowledge model tests

This suite remains independently callable until the normalized model becomes a public export.
-/

open Lean Frontier

namespace Frontier.Test

private def sameLegacyEntry (left right : Entry) : Bool :=
  left.id == right.id &&
  left.title == right.title &&
  left.summary == right.summary &&
  left.status == right.status &&
  left.literature == right.literature &&
  left.citation? == right.citation? &&
  left.topic == right.topic &&
  left.tags == right.tags &&
  left.statement == right.statement &&
  left.certificate? == right.certificate? &&
  left.evidence? == right.evidence? &&
  left.baseTheory? == right.baseTheory? &&
  left.sanityChecks == right.sanityChecks &&
  left.authors == right.authors &&
  left.tooling == right.tooling &&
  left.source? == right.source? &&
  left.created == right.created &&
  left.updated == right.updated

def testKnowledgeModel (suite : Suite) : IO Unit := do
  let legacy : Entry := {
    id := "normalized-fixture"
    title := "Normalized fixture"
    summary := "Exercises every legacy field."
    status := .disproved
    literature := .folklore
    citation? := some "A traditional source."
    topic := "logic"
    tags := #["normalization", "fixture"]
    statement := `FermatFromScratch.pow_card
    certificate? := some `FermatFromScratch.pow_card
    evidence? := some .counterexample
    baseTheory? := some "A legacy base theory description"
    sanityChecks := #[`FermatFromScratch.pow_card, `FermatFromScratch.pow_card]
    authors := #["Test Author"]
    tooling := #["Test Tool"]
    source? := some "legacy-source"
    created := "2026-01-02"
    updated := "2026-01-03"
  }
  let normalized := Knowledge.normalizeEntry legacy
  let again := Knowledge.normalizeEntry legacy

  check suite "knowledge normalization is deterministic" (normalized == again)
  check suite "claim and formulation have distinct typed deterministic IDs"
    (normalized.claim.id.value == legacy.id &&
      normalized.formalization.id.value == "normalized-fixture:formalization:primary")
  check suite "certificate conclusion is separate from method"
    ((normalized.certificate?.map fun certificate =>
      certificate.conclusion == .refutes && certificate.method == .counterexample).getD false)
  check suite "artifact authorship survives normalization"
    (normalized.formalization.authors == legacy.authors &&
      normalized.certificate?.map (·.authors) == some legacy.authors)
  check suite "legacy sanity checks receive an explicit typed fallback role"
    (normalized.sanityChecks.size == 2 &&
      normalized.sanityChecks.all (·.role == .legacyUnclassified))
  check suite "literature and citation become separate records"
    (normalized.literatureAssertion.conclusion == .folklore &&
      normalized.citation?.map (·.display) == legacy.citation? &&
      normalized.literatureAssertion.citations ==
        (normalized.citation?.map (#[·.id])).getD #[])
  check suite "normalization preserves every legacy field through projection"
    (sameLegacyEntry normalized.toLegacyEntry legacy)

  let registry := Knowledge.ofLegacy #[legacy, { legacy with
    id := "open-fixture"
    status := .open
    literature := .unresolved
    citation? := none
    certificate? := none
    evidence? := none
    baseTheory? := none
    sanityChecks := #[]
  }]
  check suite "registry aggregation preserves input order"
    (registry.claims.map (·.id.value) == #["normalized-fixture", "open-fixture"])
  check suite "registry contains only certificates and citations that exist"
    (registry.certificates.size == 1 && registry.citations.size == 1)
  check suite "registry retains one literature assertion and legacy record per entry"
    (registry.literatureAssertions.size == 2 && registry.legacy.size == 2)

end Frontier.Test
