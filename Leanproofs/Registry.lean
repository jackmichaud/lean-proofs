/-
Copyright (c) 2026 Jack Michaud. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Michaud
-/

import Lean

/-!
# Frontier theorem registry

Data types shared by the checked Lean catalog and the `frontier` CLI.
-/

namespace Frontier

/-- Research state of a formal mathematical claim. -/
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
  | .proved | .disproved | .independent | .undecidable => true
  | _ => false

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
  status : Status
  topic : String
  tags : Array String := #[]
  statement : Lean.Name
  certificate? : Option Lean.Name := none
  evidence? : Option EvidenceKind := none
  authors : Array String := #[]
  source? : Option String := none
  created : String
  updated : String
  deriving Inhabited, Repr

end Frontier
