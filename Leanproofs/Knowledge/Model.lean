/-
Copyright (c) 2026 Jack Michaud. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Michaud
-/

import Lean

/-!
# Normalized Frontier knowledge model

These records separate an informal mathematical claim from its Lean formulations, checked
certificates, literature assertions, and semantic relations. Repository verification state is
intentionally absent: it is derived by auditing certificates against their formulations.
-/

namespace Frontier.Knowledge

structure ClaimId where
  value : String
  deriving BEq, DecidableEq, Hashable, Inhabited, Repr

structure FormalizationId where
  value : String
  deriving BEq, DecidableEq, Hashable, Inhabited, Repr

structure CertificateId where
  value : String
  deriving BEq, DecidableEq, Hashable, Inhabited, Repr

structure SanityCheckId where
  value : String
  deriving BEq, DecidableEq, Hashable, Inhabited, Repr

structure CitationId where
  value : String
  deriving BEq, DecidableEq, Hashable, Inhabited, Repr

structure LiteratureAssertionId where
  value : String
  deriving BEq, DecidableEq, Hashable, Inhabited, Repr

structure RelationId where
  value : String
  deriving BEq, DecidableEq, Hashable, Inhabited, Repr

/-- The mathematical shape of a claim, independent of its proof status. -/
inductive ClaimKind where
  | ordinary
  | conditional
  | independence
  | undecidability
  deriving BEq, DecidableEq, Inhabited, Repr

/-- Human-facing mathematical knowledge, before choosing a particular formal encoding. -/
structure Claim where
  id : ClaimId
  title : String
  summary : String
  kind : ClaimKind := .ordinary
  topic : String
  tags : Array String := #[]
  authors : Array String := #[]
  /-- Curatorial context that is not a literature citation. -/
  source? : Option String := none
  created : String
  updated : String
  deriving BEq, Inhabited, Repr

/-- How a formal statement relates to the informal claim it represents. -/
inductive FormalizationRole where
  | primary
  | equivalent
  | strengthening
  | weakening
  | specialCase
  | translation
  deriving BEq, DecidableEq, Inhabited, Repr

/-- A base theory may be linked to a Lean declaration or retained as a reviewed description. -/
structure BaseTheory where
  declaration? : Option Lean.Name := none
  description : String
  deriving BEq, Inhabited, Repr

/-- The lifecycle of a formalization inside Frontier. This is independent of literature. -/
inductive RepositoryStatus where
  | formalizing
  | open
  | conditional
  | proved
  | disproved
  | independent
  | undecidable
  deriving BEq, DecidableEq, Inhabited, Repr

def RepositoryStatus.isClosed : RepositoryStatus → Bool
  | .conditional | .proved | .disproved | .independent | .undecidable => true
  | .formalizing | .open => false

/-- One Lean encoding of a claim. This record makes no assertion that a proof exists. -/
structure Formalization where
  id : FormalizationId
  claimId : ClaimId
  statement : Lean.Name
  status : RepositoryStatus
  role : FormalizationRole := .primary
  baseTheory? : Option BaseTheory := none
  /-- Humans responsible for this formal encoding. -/
  authors : Array String := #[]
  tooling : Array String := #[]
  deriving BEq, Inhabited, Repr

/-- Whether a certificate establishes the statement or its negation. -/
inductive CertificateConclusion where
  | affirms
  | refutes
  deriving BEq, DecidableEq, Inhabited, Repr

/-- The mathematical method used by a certificate, separate from its conclusion. -/
inductive CertificateMethod where
  | directProof
  | counterexample
  | conditionalProof
  | modelConstruction
  | reduction
  | metatheorem
  deriving BEq, DecidableEq, Inhabited, Repr

/-- A candidate kernel certificate. Its validity and trust state are derived by audit. -/
structure Certificate where
  id : CertificateId
  formalizationId : FormalizationId
  declaration : Lean.Name
  conclusion : CertificateConclusion
  method : CertificateMethod
  /-- Humans responsible for the certificate. -/
  authors : Array String := #[]
  tooling : Array String := #[]
  deriving BEq, Inhabited, Repr

/-- The purpose served by a checked guard against a bad formalization. -/
inductive SanityRole where
  | satisfiable
  | workedExample
  | boundaryCase
  | boundedSearch
  | nontriviality
  | correspondence
  deriving BEq, DecidableEq, Inhabited, Repr

structure SanityCheck where
  id : SanityCheckId
  formalizationId : FormalizationId
  declaration : Lean.Name
  role : SanityRole
  deriving BEq, Inhabited, Repr

structure Citation where
  id : CitationId
  display : String
  doi? : Option String := none
  url? : Option String := none
  year? : Option Nat := none
  deriving BEq, Inhabited, Repr

inductive LiteratureConclusion where
  | unresolved
  | affirmed
  | refuted
  | folklore
  deriving BEq, DecidableEq, Inhabited, Repr

/-- A reviewable statement about the external mathematical literature. -/
structure LiteratureAssertion where
  id : LiteratureAssertionId
  claimId : ClaimId
  conclusion : LiteratureConclusion
  citations : Array CitationId := #[]
  note? : Option String := none
  reviewedBy : Array String := #[]
  observed : String
  deriving BEq, Inhabited, Repr

inductive RelationKind where
  | equivalent
  | generalizes
  | specializes
  | implies
  | analogous
  | dependsConceptuallyOn
  deriving BEq, DecidableEq, Inhabited, Repr

/-- A curated semantic relation. Kernel-derived proof dependencies belong to another graph. -/
structure Relation where
  id : RelationId
  source : ClaimId
  target : ClaimId
  kind : RelationKind
  citation? : Option CitationId := none
  formalWitness? : Option Lean.Name := none
  deriving BEq, Inhabited, Repr

/-- The normalized knowledge store. Audit results are deliberately not persisted here. -/
structure Registry where
  claims : Array Claim := #[]
  formalizations : Array Formalization := #[]
  certificates : Array Certificate := #[]
  sanityChecks : Array SanityCheck := #[]
  citations : Array Citation := #[]
  literatureAssertions : Array LiteratureAssertion := #[]
  relations : Array Relation := #[]
  deriving BEq, Inhabited, Repr

private def duplicateErrors (kind : String) (ids : Array String) : Array String := Id.run do
  let mut seen : Std.HashSet String := {}
  let mut errors := #[]
  for id in ids do
    if seen.contains id then
      errors := errors.push s!"duplicate {kind} id '{id}'"
    else
      seen := seen.insert id
  return errors

/-- Structural errors in the normalized graph. Kernel and policy checks remain the audit's job. -/
def Registry.validationErrors (registry : Registry) : Array String := Id.run do
  let mut errors := #[]
  errors := errors ++ duplicateErrors "claim" (registry.claims.map (·.id.value))
  errors := errors ++ duplicateErrors "formalization" (registry.formalizations.map (·.id.value))
  errors := errors ++ duplicateErrors "certificate" (registry.certificates.map (·.id.value))
  errors := errors ++ duplicateErrors "sanity check" (registry.sanityChecks.map (·.id.value))
  errors := errors ++ duplicateErrors "citation" (registry.citations.map (·.id.value))
  errors := errors ++ duplicateErrors "literature assertion"
    (registry.literatureAssertions.map (·.id.value))
  errors := errors ++ duplicateErrors "relation" (registry.relations.map (·.id.value))

  for claim in registry.claims do
    let primaryCount := (registry.formalizations.filter fun item =>
      item.claimId == claim.id && item.role == .primary).size
    if primaryCount != 1 then
      errors := errors.push s!"claim '{claim.id.value}' has {primaryCount} primary formalizations"
    if !(registry.literatureAssertions.any (·.claimId == claim.id)) then
      errors := errors.push s!"claim '{claim.id.value}' has no literature assertion"
  for formalization in registry.formalizations do
    if !(registry.claims.any (·.id == formalization.claimId)) then
      errors := errors.push s!"formalization '{formalization.id.value}' references an unknown claim"
    let attached := registry.certificates.filter (·.formalizationId == formalization.id)
    if formalization.status.isClosed && attached.size != 1 then
      errors := errors.push s!"closed formalization '{formalization.id.value}' must have one certificate"
    if !formalization.status.isClosed && !attached.isEmpty then
      errors := errors.push s!"open formalization '{formalization.id.value}' cannot have a certificate"
    for certificate in attached do
      let expected := if formalization.status == .disproved then .refutes else .affirms
      if certificate.conclusion != expected then
        errors := errors.push s!"certificate '{certificate.id.value}' has the wrong conclusion"
    if let some claim := registry.claims.find? (·.id == formalization.claimId) then
      let kindMatches := match formalization.status with
        | .conditional => claim.kind == .conditional
        | .independent => claim.kind == .independence
        | .undecidable => claim.kind == .undecidability
        | _ => true
      if !kindMatches then
        errors := errors.push s!"formalization '{formalization.id.value}' disagrees with its claim kind"
  for certificate in registry.certificates do
    if !(registry.formalizations.any (·.id == certificate.formalizationId)) then
      errors := errors.push s!"certificate '{certificate.id.value}' references an unknown formalization"
  for check in registry.sanityChecks do
    if !(registry.formalizations.any (·.id == check.formalizationId)) then
      errors := errors.push s!"sanity check '{check.id.value}' references an unknown formalization"
  for assertion in registry.literatureAssertions do
    if !(registry.claims.any (·.id == assertion.claimId)) then
      errors := errors.push s!"literature assertion '{assertion.id.value}' references an unknown claim"
    for citationId in assertion.citations do
      if !(registry.citations.any (·.id == citationId)) then
        errors := errors.push s!"literature assertion '{assertion.id.value}' references an unknown citation"
  for relation in registry.relations do
    if !(registry.claims.any (·.id == relation.source)) ||
        !(registry.claims.any (·.id == relation.target)) then
      errors := errors.push s!"relation '{relation.id.value}' references an unknown claim"
    if let some citationId := relation.citation? then
      if !(registry.citations.any (·.id == citationId)) then
        errors := errors.push s!"relation '{relation.id.value}' references an unknown citation"
  return errors

end Frontier.Knowledge
