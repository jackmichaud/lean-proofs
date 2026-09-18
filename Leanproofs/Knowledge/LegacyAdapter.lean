/-
Copyright (c) 2026 Jack Michaud. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Michaud
-/

import Leanproofs.Knowledge.Model

/-!
# Legacy registry adapter

The adapter is deterministic and intentionally conservative. It records legacy classifications
verbatim when the old schema carries meaning the normalized model cannot safely infer.
-/

namespace Frontier.Knowledge

private def generatedId (entryId suffix : String) : String := entryId ++ ":" ++ suffix

def claimIdOf (entry : Frontier.Entry) : ClaimId := ⟨entry.id⟩

def formalizationIdOf (entry : Frontier.Entry) : FormalizationId :=
  ⟨generatedId entry.id "formalization:primary"⟩

def certificateIdOf (entry : Frontier.Entry) : CertificateId :=
  ⟨generatedId entry.id "certificate:legacy"⟩

def citationIdOf (entry : Frontier.Entry) : CitationId :=
  ⟨generatedId entry.id "citation:legacy"⟩

def literatureAssertionIdOf (entry : Frontier.Entry) : LiteratureAssertionId :=
  ⟨generatedId entry.id "literature:legacy"⟩

def sanityCheckIdOf (entry : Frontier.Entry) (index : Nat) : SanityCheckId :=
  ⟨generatedId entry.id s!"sanity:{index}"⟩

private def claimKindOfStatus : Frontier.Status → ClaimKind
  | .conditional => .conditional
  | .independent => .independence
  | .undecidable => .undecidability
  | _ => .ordinary

private def literatureConclusionOf : Frontier.Literature → LiteratureConclusion
  | .unresolved => .unresolved
  | .proved => .affirmed
  | .disproved => .refuted
  | .folklore => .folklore

private def certificateConclusionOf (status : Frontier.Status) : CertificateConclusion :=
  if status == .disproved then .refutes else .affirms

private def certificateMethodOf : Option Frontier.EvidenceKind → CertificateMethod
  | some .proof => .directProof
  | some .counterexample => .counterexample
  | some .conditionalProof => .conditionalProof
  | some .modelConstruction => .modelConstruction
  | some .reduction => .reduction
  | some .metatheorem => .metatheorem
  | none => .legacyUnclassified

/-- The records generated from one legacy entry before flattening into a `Registry`. -/
structure NormalizedEntry where
  claim : Claim
  formalization : Formalization
  certificate? : Option Certificate
  sanityChecks : Array SanityCheck
  citation? : Option Citation
  literatureAssertion : LiteratureAssertion
  legacy : LegacyMetadata
  deriving BEq, Inhabited, Repr

/-- Normalize one legacy entry without auditing or strengthening any authored assertion. -/
def normalizeEntry (entry : Frontier.Entry) : NormalizedEntry :=
  let claimId := claimIdOf entry
  let formalizationId := formalizationIdOf entry
  let citation? := entry.citation?.map fun display => {
    id := citationIdOf entry
    display := display
  }
  {
    claim := {
      id := claimId
      title := entry.title
      summary := entry.summary
      kind := claimKindOfStatus entry.status
      topic := entry.topic
      tags := entry.tags
      authors := entry.authors
      created := entry.created
      updated := entry.updated
    }
    formalization := {
      id := formalizationId
      claimId := claimId
      statement := entry.statement
      baseTheory? := entry.baseTheory?.map fun description => { description := description }
      authors := entry.authors
      tooling := entry.tooling
    }
    certificate? := entry.certificate?.map fun declaration => {
      id := certificateIdOf entry
      formalizationId := formalizationId
      declaration := declaration
      conclusion := certificateConclusionOf entry.status
      method := certificateMethodOf entry.evidence?
      authors := entry.authors
      tooling := entry.tooling
    }
    sanityChecks := entry.sanityChecks.mapIdx fun index declaration => {
      id := sanityCheckIdOf entry index
      formalizationId := formalizationId
      declaration := declaration
      role := .legacyUnclassified
    }
    citation? := citation?
    literatureAssertion := {
      id := literatureAssertionIdOf entry
      claimId := claimId
      conclusion := literatureConclusionOf entry.literature
      citations := citation?.map (#[·.id]) |>.getD #[]
      observed := entry.updated
    }
    legacy := {
      claimId := claimId
      status := entry.status
      literature := entry.literature
      citation? := entry.citation?
      evidence? := entry.evidence?
      baseTheory? := entry.baseTheory?
      source? := entry.source?
    }
  }

/-- Flatten legacy entries in input order. Generated IDs depend only on the source entry ID. -/
def ofLegacy (entries : Array Frontier.Entry) : Registry :=
  entries.foldl (init := {}) fun registry entry =>
    let normalized := normalizeEntry entry
    { registry with
      claims := registry.claims.push normalized.claim
      formalizations := registry.formalizations.push normalized.formalization
      certificates := normalized.certificate?.map registry.certificates.push
        |>.getD registry.certificates
      sanityChecks := registry.sanityChecks ++ normalized.sanityChecks
      citations := normalized.citation?.map registry.citations.push |>.getD registry.citations
      literatureAssertions :=
        registry.literatureAssertions.push normalized.literatureAssertion
      legacy := registry.legacy.push normalized.legacy }

/-- Reconstruct the source shape for migration parity tests and compatibility exports. -/
def NormalizedEntry.toLegacyEntry (entry : NormalizedEntry) : Frontier.Entry := {
  id := entry.claim.id.value
  title := entry.claim.title
  summary := entry.claim.summary
  status := entry.legacy.status
  literature := entry.legacy.literature
  citation? := entry.legacy.citation?
  topic := entry.claim.topic
  tags := entry.claim.tags
  statement := entry.formalization.statement
  certificate? := entry.certificate?.map (·.declaration)
  evidence? := entry.legacy.evidence?
  baseTheory? := entry.legacy.baseTheory?
  sanityChecks := entry.sanityChecks.map (·.declaration)
  authors := entry.claim.authors
  tooling := entry.formalization.tooling
  source? := entry.legacy.source?
  created := entry.claim.created
  updated := entry.claim.updated
}

end Frontier.Knowledge
