/-
Copyright (c) 2026 Jack Michaud. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Michaud
-/

import Leanproofs.Registry

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

/-- One Lean encoding of a claim. This record makes no assertion that a proof exists. -/
structure Formalization where
  id : FormalizationId
  claimId : ClaimId
  statement : Lean.Name
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
  | legacyUnclassified
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
  /-- Used by the adapter because legacy entries did not record a role. -/
  | legacyUnclassified
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

/-- Compatibility-only fields whose legacy meaning cannot be faithfully inferred. -/
structure LegacyMetadata where
  claimId : ClaimId
  status : Frontier.Status
  literature : Frontier.Literature
  citation? : Option String
  evidence? : Option Frontier.EvidenceKind
  baseTheory? : Option String
  source? : Option String
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
  legacy : Array LegacyMetadata := #[]
  deriving BEq, Inhabited, Repr

end Frontier.Knowledge
