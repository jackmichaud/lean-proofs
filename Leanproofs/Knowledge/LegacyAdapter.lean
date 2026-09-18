/-
Copyright (c) 2026 Jack Michaud. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Michaud
-/

import Leanproofs.Knowledge.Model
import Leanproofs.Registry

/-!
# Legacy audit projection

`Knowledge.Registry` is authoritative. This module contains the temporary one-way projection
needed by the existing CLI and trust audit while those consumers still operate on `Entry`.
-/

namespace Frontier.Knowledge

private def toStatus : RepositoryStatus → Frontier.Status
  | .formalizing => .formalizing
  | .open => .open
  | .conditional => .conditional
  | .proved => .proved
  | .disproved => .disproved
  | .independent => .independent
  | .undecidable => .undecidable

private def toLiterature : LiteratureConclusion → Frontier.Literature
  | .unresolved => .unresolved
  | .affirmed => .proved
  | .refuted => .disproved
  | .folklore => .folklore

private def toEvidence : CertificateMethod → Option Frontier.EvidenceKind
  | .directProof => some .proof
  | .counterexample => some .counterexample
  | .conditionalProof => some .conditionalProof
  | .modelConstruction => some .modelConstruction
  | .reduction => some .reduction
  | .metatheorem => some .metatheorem
  | .legacyUnclassified => none

private def Registry.primaryFormalization? (registry : Registry)
    (claimId : ClaimId) : Option Formalization :=
  registry.formalizations.find? fun item => item.claimId == claimId && item.role == .primary

private def Registry.literatureAssertion? (registry : Registry)
    (claimId : ClaimId) : Option LiteratureAssertion :=
  registry.literatureAssertions.foldl (init := none) fun result assertion =>
    if assertion.claimId == claimId then some assertion else result

private def Registry.citationDisplay? (registry : Registry)
    (assertion : LiteratureAssertion) : Option String :=
  assertion.citations.foldl (init := none) fun result citationId =>
    result.orElse fun _ => (registry.citations.find? (·.id == citationId)).map (·.display)

private def Registry.projectClaim? (registry : Registry) (claim : Claim) : Option Frontier.Entry := do
  let formalization ← registry.primaryFormalization? claim.id
  let assertion ← registry.literatureAssertion? claim.id
  let certificate? := registry.certificates.find? (·.formalizationId == formalization.id)
  let checks := registry.sanityChecks.filter (·.formalizationId == formalization.id)
  return {
    id := claim.id.value
    title := claim.title
    summary := claim.summary
    status := toStatus formalization.status
    literature := toLiterature assertion.conclusion
    citation? := registry.citationDisplay? assertion
    topic := claim.topic
    tags := claim.tags
    statement := formalization.statement
    certificate? := certificate?.map (·.declaration)
    evidence? := certificate?.bind (toEvidence ·.method)
    baseTheory? := formalization.baseTheory?.map (·.description)
    sanityChecks := checks.map (·.declaration)
    authors := claim.authors
    tooling := formalization.tooling
    source? := claim.source?
    created := claim.created
    updated := claim.updated
  }

/-- Project canonical records into the legacy shape consumed by the current audit and CLI. -/
def Registry.toEntries (registry : Registry) : Array Frontier.Entry :=
  registry.claims.filterMap registry.projectClaim?

end Frontier.Knowledge
