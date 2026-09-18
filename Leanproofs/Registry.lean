/-
Copyright (c) 2026 Jack Michaud. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Michaud
-/

import Leanproofs.Knowledge.Model

/-!
# Frontier registry queries

Runtime consumers operate on `Knowledge.Registry` directly. `RegisteredClaim` is a joined view
over records that remain owned by that normalized registry; it is not a second catalog schema.
-/

namespace Frontier.Knowledge

def RepositoryStatus.toString : RepositoryStatus → String
  | .formalizing => "formalizing"
  | .open => "open"
  | .conditional => "conditional"
  | .proved => "proved"
  | .disproved => "disproved"
  | .independent => "independent"
  | .undecidable => "undecidable"

def RepositoryStatus.isRelative : RepositoryStatus → Bool
  | .independent | .undecidable => true
  | _ => false

def LiteratureConclusion.toString : LiteratureConclusion → String
  | .unresolved => "unresolved"
  | .affirmed => "proved"
  | .refuted => "disproved"
  | .folklore => "folklore"

def LiteratureConclusion.requiresCitation : LiteratureConclusion → Bool
  | .unresolved => false
  | .affirmed | .refuted | .folklore => true

def CertificateMethod.toString : CertificateMethod → String
  | .directProof => "proof"
  | .counterexample => "counterexample"
  | .conditionalProof => "conditional-proof"
  | .modelConstruction => "model-construction"
  | .reduction => "reduction"
  | .metatheorem => "metatheorem"

/-- The normalized records associated with one claim's primary formalization. -/
structure RegisteredClaim where
  claim : Claim
  formalization : Formalization
  certificate? : Option Certificate
  sanityChecks : Array SanityCheck
  literature? : Option LiteratureAssertion
  citations : Array Citation
  deriving Inhabited, Repr

def RegisteredClaim.id (entry : RegisteredClaim) : String := entry.claim.id.value
def RegisteredClaim.title (entry : RegisteredClaim) : String := entry.claim.title
def RegisteredClaim.summary (entry : RegisteredClaim) : String := entry.claim.summary
def RegisteredClaim.topic (entry : RegisteredClaim) : String := entry.claim.topic
def RegisteredClaim.tags (entry : RegisteredClaim) : Array String := entry.claim.tags
def RegisteredClaim.statement (entry : RegisteredClaim) : Lean.Name := entry.formalization.statement
def RegisteredClaim.status (entry : RegisteredClaim) : RepositoryStatus := entry.formalization.status

def RegisteredClaim.literature (entry : RegisteredClaim) : LiteratureConclusion :=
  entry.literature?.map (·.conclusion) |>.getD .unresolved

def RegisteredClaim.citation? (entry : RegisteredClaim) : Option String :=
  entry.citations[0]?.map (·.display)

def RegisteredClaim.baseTheory? (entry : RegisteredClaim) : Option String :=
  entry.formalization.baseTheory?.map (·.description)

def Registry.primaryFormalization? (registry : Registry) (claimId : ClaimId) : Option Formalization :=
  registry.formalizations.find? fun item => item.claimId == claimId && item.role == .primary

def Registry.literatureAssertion? (registry : Registry)
    (claimId : ClaimId) : Option LiteratureAssertion :=
  registry.literatureAssertions.find? (·.claimId == claimId)

def Registry.registeredClaim? (registry : Registry) (claim : Claim) : Option RegisteredClaim := do
  let formalization ← registry.primaryFormalization? claim.id
  let literature? := registry.literatureAssertion? claim.id
  let citationIds := literature?.map (·.citations) |>.getD #[]
  return {
    claim
    formalization
    certificate? := registry.certificates.find? (·.formalizationId == formalization.id)
    sanityChecks := registry.sanityChecks.filter (·.formalizationId == formalization.id)
    literature?
    citations := citationIds.filterMap fun id => registry.citations.find? (·.id == id)
  }

def Registry.entries (registry : Registry) : Array RegisteredClaim :=
  registry.claims.filterMap registry.registeredClaim?

def Registry.findClaim? (registry : Registry) (id : String) : Option RegisteredClaim := do
  let claim ← registry.claims.find? (·.id.value == id)
  registry.registeredClaim? claim

/- These collection-shaped helpers keep generic runtime code concise while iteration remains a
view over the normalized records. -/
def Registry.map (registry : Registry) (f : RegisteredClaim → α) : Array α :=
  registry.entries.map f

def Registry.toList (registry : Registry) : List RegisteredClaim := registry.entries.toList

def Registry.size (registry : Registry) : Nat := registry.claims.size

/-- Whether `value` is an ISO-8601 calendar date, `YYYY-MM-DD`. -/
def isIsoDate (value : String) : Bool := Id.run do
  let characters := value.toList
  if characters.length != 10 then return false
  let digitsAt (positions : List Nat) : Bool :=
    positions.all fun index => (characters[index]?.map Char.isDigit).getD false
  let dashesAt (positions : List Nat) : Bool :=
    positions.all fun index => characters[index]? == some '-'
  if !digitsAt [0, 1, 2, 3, 5, 6, 8, 9] || !dashesAt [4, 7] then return false
  let number (from_ len : Nat) : Nat :=
    (List.range len).foldl (init := 0) fun total offset =>
      total * 10 + ((characters[from_ + offset]?.map fun c => c.toNat - '0'.toNat).getD 0)
  let month := number 5 2
  let day := number 8 2
  return 1 ≤ month && month ≤ 12 && 1 ≤ day && day ≤ 31

end Frontier.Knowledge

namespace Frontier

abbrev isIsoDate := Knowledge.isIsoDate

end Frontier
