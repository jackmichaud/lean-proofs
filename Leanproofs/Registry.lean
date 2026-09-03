/-
Copyright (c) 2026 Jack Michaud. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Michaud
-/

import Lean

/-!
# Frontier theorem registry

Data types shared by the checked Lean catalog and the `frontier` CLI.

Two independent axes describe every record:

* `Status` is the *Frontier* state: what this repository has formalized and checked.
* `Literature` is the *mathematical* state: what the research literature already knows.

Keeping them separate is the point of the registry. "Nobody has proved this" and "we have not
typed this in yet" are opposite conditions, and conflating them makes the research frontier
unreadable.
-/

namespace Frontier

/-- Formalization state of a claim *inside this repository*. -/
inductive Status where
  | formalizing
  | open
  | conditional
  | proved
  | disproved
  | independent
  | undecidable
  deriving BEq, DecidableEq, Inhabited, Repr

def Status.toString : Status → String
  | .formalizing => "formalizing"
  | .open => "open"
  | .conditional => "conditional"
  | .proved => "proved"
  | .disproved => "disproved"
  | .independent => "independent"
  | .undecidable => "undecidable"

def Status.isClosed : Status → Bool
  | .conditional | .proved | .disproved | .independent | .undecidable => true
  | _ => false

/-- Whether the status is a relative metamathematical classification, which is meaningless
without a named base theory. -/
def Status.isRelative : Status → Bool
  | .independent | .undecidable => true
  | _ => false

/-- State of the claim *in the mathematical literature*, independent of what Frontier has
formalized. A theorem can be `Literature.proved` and `Status.open` at the same time: that is
exactly the "known result, not yet formalized here" case. -/
inductive Literature where
  /-- No published resolution is known to the maintainers. A genuine research frontier. -/
  | unresolved
  /-- Resolved affirmatively in the literature. Requires a citation. -/
  | proved
  /-- Refuted in the literature. Requires a citation. -/
  | disproved
  /-- Widely known and used but without a canonical citation. Requires a note. -/
  | folklore
  deriving BEq, DecidableEq, Inhabited, Repr

def Literature.toString : Literature → String
  | .unresolved => "unresolved"
  | .proved => "proved"
  | .disproved => "disproved"
  | .folklore => "folklore"

/-- Literature states that make a claim about existing mathematics, and therefore must name a
source. -/
def Literature.requiresCitation : Literature → Bool
  | .unresolved => false
  | .proved | .disproved | .folklore => true

/-- The kind of kernel-checked evidence attached to a closed claim. -/
inductive EvidenceKind where
  | proof
  | counterexample
  | conditionalProof
  | modelConstruction
  | reduction
  | metatheorem
  deriving BEq, DecidableEq, Inhabited, Repr

def EvidenceKind.toString : EvidenceKind → String
  | .proof => "proof"
  | .counterexample => "counterexample"
  | .conditionalProof => "conditional-proof"
  | .modelConstruction => "model-construction"
  | .reduction => "reduction"
  | .metatheorem => "metatheorem"

/-- A theorem, conjecture, disproof, or metamathematical classification tracked by Frontier. -/
structure Entry where
  id : String
  title : String
  summary : String
  /-- What this repository has checked. See `Literature` for what mathematics knows. -/
  status : Status
  /-- What the mathematical literature knows, independent of `status`. -/
  literature : Literature := .unresolved
  /-- Reference supporting `literature`. Required unless `literature = .unresolved`. -/
  citation? : Option String := none
  topic : String
  tags : Array String := #[]
  statement : Lean.Name
  certificate? : Option Lean.Name := none
  evidence? : Option EvidenceKind := none
  /-- The explicitly formalized theory or decision problem that an `independent` or
  `undecidable` classification is relative to. Required for those statuses; those words are
  never absolute labels. -/
  baseTheory? : Option String := none
  /-- Checked lemmas that guard against mis-formalization: witnesses that the hypotheses are
  satisfiable, worked instances, boundary cases. These are validated but are not research
  results and are never counted as such. -/
  sanityChecks : Array Lean.Name := #[]
  /-- Humans responsible for the claim. -/
  authors : Array String := #[]
  /-- Automated tools used to produce the formalization. Tools are not authors. -/
  tooling : Array String := #[]
  source? : Option String := none
  /-- ISO-8601 `YYYY-MM-DD`. -/
  created : String
  /-- ISO-8601 `YYYY-MM-DD`. -/
  updated : String
  deriving Inhabited, Repr

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

end Frontier
