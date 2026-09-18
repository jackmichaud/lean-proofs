/-
Copyright (c) 2026 Jack Michaud. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Michaud
-/

import Leanproofs.Tests.Support

/-!
# Trust and audit tests
-/

open Lean Frontier Frontier.CLI

namespace Frontier.Test

/-! ## Axiom policy

These are pure and are the highest-value tests in the file: the policy is what stands between
an agent optimizing for a green build and an unsound catalog. -/

def testAxiomPolicy (suite : Suite) : IO Unit := do
  check suite "the three classical axioms are allowed"
    (axiomPolicyErrors "x" #[``propext, ``Classical.choice, ``Quot.sound]).isEmpty
  check suite "sorryAx is rejected"
    ((axiomPolicyErrors "x" #[``sorryAx]).size == 1)
  check suite "sorryAx is rejected for being incomplete"
    ((deniedAxiomReason? ``sorryAx).any (containsSubstring · "incomplete"))
  check suite "Lean.ofReduceBool is rejected"
    ((axiomPolicyErrors "x" #[`Lean.ofReduceBool]).size == 1)
  check suite "Lean.trustCompiler is rejected"
    ((axiomPolicyErrors "x" #[`Lean.trustCompiler]).size == 1)
  -- The regression that motivates an allowlist: current Lean does not emit `ofReduceBool` for
  -- `native_decide`, it emits a fresh per-declaration axiom. A denylist would wave this
  -- through, which is the single most dangerous thing this policy can get wrong.
  let native := `Foo._native.native_decide.ax_1_1
  check suite "a per-declaration native_decide axiom is rejected"
    ((axiomPolicyErrors "x" #[native]).size == 1)
  check suite "a per-declaration native_decide axiom is rejected by name, with a reason"
    ((deniedAxiomReason? native).any (containsSubstring · "native_decide"))
  -- Anything unrecognized is an error rather than a note, so a new axiom cannot arrive
  -- silently with a toolchain bump.
  check suite "an unknown axiom is rejected"
    ((axiomPolicyErrors "x" #[`Some.Brand.New.Axiom]).size == 1)
  check suite "an unknown axiom names the allowlist"
    (containsSubstring (axiomPolicyErrors "x" #[`Some.Brand.New.Axiom])[0]! "allowlist")
  check suite "the role is attributed in the message"
    (containsSubstring (axiomPolicyErrors "certificate 'c'" #[``sorryAx])[0]! "certificate 'c'")

/-! ## Date and identifier validation -/

def testMetadataPredicates (suite : Suite) : IO Unit := do
  check suite "a well-formed date is accepted" (isIsoDate "2026-08-31")
  check suite "a 13th month is rejected" (!isIsoDate "2026-13-01")
  check suite "a 32nd day is rejected" (!isIsoDate "2026-01-32")
  check suite "a zero month is rejected" (!isIsoDate "2026-00-10")
  check suite "a short date is rejected" (!isIsoDate "2026-8-1")
  check suite "a slash-separated date is rejected" (!isIsoDate "2026/08/31")
  check suite "an empty date is rejected" (!isIsoDate "")
  check suite "duplicate ids are reported"
    ((duplicateIdErrors #[baseEntry, baseEntry]).size == 1)
  check suite "distinct ids are accepted"
    (duplicateIdErrors #[baseEntry, { baseEntry with id := "other" }]).isEmpty

/-! ## Entry audit -/

def testEntryAudit (suite : Suite) (context : Context) : IO Unit := do
  -- Positive control. If this fails, every negative result below is meaningless.
  expectValid suite "the base fixture is valid" (← audit context baseEntry)

  expectError suite "a missing statement declaration is reported"
    (← audit context { baseEntry with statement := `No.Such.Declaration }) "does not exist"

  expectError suite "a missing certificate declaration is reported"
    (← audit context { baseEntry with certificate? := some `No.Such.Declaration })
    "does not exist"

  -- A statement that is not a proposition cannot be evidence for anything.
  expectError suite "a non-proposition statement is reported"
    (← audit context { baseEntry with statement := `Nat.succ }) "does not denote a proposition"

  -- The certificate must actually prove the registered claim, not merely exist.
  expectError suite "a certificate that does not prove the statement is reported"
    (← audit context { baseEntry with statement := `Catalan.conjecture })
    "does not match"

  -- `Catalan.conjecture` is a `def _ : Prop`, not a theorem, so it cannot certify anything.
  expectError suite "a certificate that is not a theorem is reported"
    (← audit context
      { baseEntry with statement := `Catalan.conjecture
                       certificate? := some `Catalan.conjecture })
    "is not a Lean theorem"

  expectError suite "a closed status without a certificate is reported"
    (← audit context { baseEntry with certificate? := none, evidence? := none })
    "requires a certificate"

  expectError suite "an open status with a certificate is reported"
    (← audit context { baseEntry with status := .open })
    "cannot have a closing certificate"

  expectError suite "an evidence kind without a certificate is reported"
    (← audit context { baseEntry with certificate? := none })
    "requires a certificate"

  expectError suite "a certificate without an evidence kind is reported"
    (← audit context { baseEntry with evidence? := none })
    "requires an evidence kind"

  expectError suite "evidence incompatible with the status is reported"
    (← audit context { baseEntry with evidence? := some .counterexample })
    "is incompatible with status"

  -- An unresolved entry has no certificate whose type-checking would catch a
  -- mis-formalization, so a sanity check is the only defence and is mandatory.
  expectError suite "an unresolved entry without sanity checks is reported"
    (← audit context
      { baseEntry with status := .open, certificate? := none, evidence? := none
                       statement := `Catalan.conjecture })
    "at least one sanity check"

  check suite "an unresolved entry with a sanity check passes that check"
    (!((← audit context
        { baseEntry with status := .open, certificate? := none, evidence? := none
                         statement := `Catalan.conjecture
                         sanityChecks := #[`Catalan.exceptional_solution] }).errors.any
      (containsSubstring · "at least one sanity check")))

  expectError suite "a missing sanity-check declaration is reported"
    (← audit context { baseEntry with sanityChecks := #[`No.Such.Check] }) "does not exist"

  expectError suite "a sanity check that is not a theorem is reported"
    (← audit context { baseEntry with sanityChecks := #[`Catalan.conjecture] })
    "is not a Lean theorem"

  -- `undecidable` and `independent` are relative claims; without a named theory they are not
  -- claims at all.
  expectError suite "a relative status without a base theory is reported"
    (← audit context { baseEntry with status := .undecidable, evidence? := some .metatheorem })
    "must name the formalized base theory"

  check suite "a relative status with a base theory passes that check"
    (!((← audit context
        { baseEntry with status := .undecidable, evidence? := some .metatheorem
                         baseTheory? := some "Peano arithmetic" }).errors.any
      (containsSubstring · "must name the formalized base theory")))

  expectError suite "a literature claim without a citation is reported"
    (← audit context { baseEntry with citation? := none }) "requires a citation"

  expectError suite "a blank citation is reported"
    (← audit context { baseEntry with citation? := some "   " }) "requires a citation"

  check suite "an unresolved literature state needs no citation"
    (!((← audit context
        { baseEntry with literature := .unresolved, citation? := none }).errors.any
      (containsSubstring · "requires a citation")))

  expectError suite "folklore without a citation is reported"
    (← audit context { baseEntry with literature := .folklore, citation? := none })
    "requires a citation"

  -- Proved here and refuted in the literature cannot both be true.
  expectError suite "a status/literature contradiction is reported"
    (← audit context { baseEntry with literature := .disproved }) "while the literature field"

  expectError suite "a malformed created date is reported"
    (← audit context { baseEntry with created := "2026-13-01" }) "is not an ISO-8601"

  expectError suite "a malformed updated date is reported"
    (← audit context { baseEntry with updated := "31/08/2026" }) "is not an ISO-8601"

  expectError suite "an entry with no author is reported"
    (← audit context { baseEntry with authors := #[] }) "at least one human author"

  expectError suite "a blank title is reported"
    (← audit context { baseEntry with title := "  " }) "title cannot be empty"

  expectError suite "a blank id is reported"
    (← audit context { baseEntry with id := "" }) "id cannot be empty"

  -- Statements are audited, not just certificates: an `open` entry has no certificate whose
  -- type-checking would catch a statement built out of `sorry`. The catalog-side half of this
  -- cannot be fixture-tested without putting a poisoned declaration into the build, so what is
  -- asserted here is that the statement's axioms are computed and reported at all. The
  -- rejection itself is covered against a real `sorry` by `testDraftChecking` below.
  check suite "a statement's axioms are audited and reported"
    (!(← audit context baseEntry).statementAxioms.isEmpty)
  -- An open conjecture is a `def _ : Prop`, whose *type* is just `Prop` and carries no
  -- mathematics. The audit has to record the denoted body, or the registry displays every open
  -- problem as the word "Prop".
  let openAudit ← audit context
    { baseEntry with status := .open, certificate? := none, evidence? := none
                     statement := `Catalan.conjecture
                     sanityChecks := #[`Catalan.exceptional_solution] }
  check suite "an open entry records the proposition its statement denotes, not `Prop`"
    (openAudit.statementType != "Prop" && containsSubstring openAudit.statementType "∀")
    s!"got {openAudit.statementType}"

/-! ## Dependency extraction -/

def testDependencies (suite : Suite) (context : Context) : IO Unit := do
  let (audits, globalErrors) ← auditCatalog context
  check suite "the committed catalog audits cleanly"
    (globalErrors.isEmpty && audits.all Audit.isValid)
    s!"{(audits.filter (fun item => !item.isValid)).map (·.entry.id)} failed; global: {globalErrors}"

  -- Minimal ancestors, not transitive closure: `fermat-zmod` is built on
  -- `fermat-zmod-nonzero`, which is built on `fermat-units`. If the walk did not stop at
  -- registered declarations, `fermat-zmod` would list both and the graph would say nothing.
  let some zmod := audits.find? (·.entry.id == "fermat-zmod")
    | check suite "fermat-zmod is in the catalog" false
  check suite "dependencies are minimal catalog ancestors"
    (zmod.dependencies == #["fermat-zmod-nonzero"])
    s!"expected #[fermat-zmod-nonzero], got {zmod.dependencies}"

  check suite "an entry is not its own dependency"
    (audits.all fun item => !(item.dependencies.contains item.entry.id))

  -- Axioms must be collected *through* registered intermediates, or an axiom could hide
  -- beneath a catalog entry and never be audited again.
  check suite "axioms are collected through registered intermediates"
    (zmod.axioms.size > 0) s!"expected inherited axioms, got {zmod.axioms}"

  -- Circular-premise exclusion for `suggest`.
  let closure := dependentClosure audits "fermat-units"
  check suite "the dependent closure contains the entry itself" (closure.contains "fermat-units")
  check suite "the dependent closure contains a direct dependent"
    (closure.contains "fermat-zmod-nonzero")
  check suite "the dependent closure is transitive, not just direct"
    (closure.contains "fermat-zmod")
  let leaf := dependentClosure audits "fermat-integer"
  check suite "a leaf entry has no dependents beyond itself" (leaf.size == 1)
  check suite "excluded declarations cover the closure"
    ((registeredDeclarations context.catalog closure).contains
      `FermatFromScratch.units_pow_card_sub_one_eq_one)
  check suite "excluded declarations cover sanity checks"
    ((registeredDeclarations context.catalog
      (({} : Std.HashSet String).insert "catalan-conjecture")).contains
        `Catalan.exceptional_solution)

end Frontier.Test

