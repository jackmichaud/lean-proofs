/-
Copyright (c) 2026 Jack Michaud. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Michaud
-/

import Leanproofs.Tests.Support

/-!
# Draft and retrieval tests
-/

open Lean Frontier Frontier.CLI

namespace Frontier.Test

/-! ## Draft checking

Fixtures are written to disk and elaborated, which is the only way to test the `sorry` and
`native_decide` paths without putting either into the build. -/


def testDraftChecking (suite : Suite) (context : Context) : IO Unit := do
  let budget := defaultDraftHeartbeats

  -- A clean draft, including the catalog reuse an agent needs reported back.
  withDraft
    "import Mathlib.Data.ZMod.Basic\n\n\
     theorem draft_ok (p : ℕ) [Fact p.Prime] (a : ZMod p) : (a ^ p) ^ p = a := by\n  \
     rw [FermatFromScratch.pow_card, FermatFromScratch.pow_card]\n"
    fun path => do
      let report ← checkDraft context path budget
      check suite "a clean draft is accepted" report.isClean
        s!"fatal: {report.fatal}, diagnostics: {report.diagnostics}"
      check suite "a clean draft reports its declaration" (report.declarations.size == 1)
      check suite "a clean draft reports catalog reuse"
        (report.declarations.any (·.dependencies.contains "fermat-zmod"))
        s!"got {report.declarations.map (·.dependencies)}"

  -- The reason the draft loop exists: `sorry` must not read as clean.
  withDraft "theorem draft_sorry (n : Nat) : n + 0 = n := by sorry\n" fun path => do
    let report ← checkDraft context path budget
    check suite "a sorry draft is rejected" (!report.isClean)
    check suite "a sorry draft reports the sorryAx policy violation"
      (report.declarations.any fun declaration =>
        declaration.errors.any (containsSubstring · "sorryAx"))
      s!"got {report.declarations.map (·.errors)}"

  -- The soundness hole an agent optimizing for a green build finds first.
  withDraft
    "import Mathlib.Data.Nat.Basic\n\n\
     theorem draft_native : (List.range 200).length = 200 := by native_decide\n"
    fun path => do
      let report ← checkDraft context path budget
      check suite "a native_decide draft is rejected" (!report.isClean)
      check suite "a native_decide draft explains why"
        (report.declarations.any fun declaration =>
          declaration.errors.any (containsSubstring · "native_decide"))
        s!"got {report.declarations.map (·.errors)}"

  -- The exact hole that motivates auditing statements rather than only certificates: an open
  -- conjecture is registered as a `def _ : Prop`, and nothing about a `def` forces a proof to
  -- exist. Built out of `sorry`, it must not read as clean.
  withDraft "def draft_claim : Prop := (sorry : Prop)\n" fun path => do
    let report ← checkDraft context path budget
    check suite "a Prop-valued definition built from sorry is rejected" (!report.isClean)
    check suite "a sorry-built definition reports the policy violation"
      (report.declarations.any fun declaration =>
        declaration.errors.any (containsSubstring · "sorryAx"))
      s!"got {report.declarations.map (·.errors)}"

  withDraft "theorem draft_broken : Nat := by exact\n" fun path => do
    let report ← checkDraft context path budget
    check suite "a draft that does not elaborate is rejected" (!report.isClean)
    check suite "a draft that does not elaborate reports diagnostics"
      (report.hasErrors && report.diagnostics.size > 0)

  -- A draft cannot pull in modules the loaded environment does not have, and saying so
  -- explicitly is the difference between one message and an unknown-identifier cascade.
  withDraft "import Not.A.Real.Module\n\ntheorem draft_import : True := trivial\n" fun path => do
    let report ← checkDraft context path budget
    check suite "a draft importing an unavailable module is rejected" (!report.isClean)
    check suite "an unavailable import is reported as fatal"
      (report.fatal.any (containsSubstring · "not in the loaded environment"))
      s!"got {report.fatal}"
    -- And nothing else. Elaborating anyway reports every use of the missing module as an
    -- unknown identifier, printing the cascade underneath the one message that explains it —
    -- and a draft whose missing import happens not to matter elaborates clean, so the report
    -- would list declarations beside a fatal error.
    check suite "an unavailable import stops before elaboration"
      (report.declarations.isEmpty && !report.hasErrors && report.diagnostics.isEmpty)
      s!"declarations: {report.declarations.map (·.name)}, diagnostics: {report.diagnostics}"

  let report ← checkDraft context "build/test-drafts/definitely-absent.lean" budget
  check suite "a missing draft file is reported"
    (report.fatal.any (containsSubstring · "does not exist"))

/-! ## Goal elaboration -/

def testGoalElaboration (suite : Suite) (context : Context) : IO Unit := do
  match ← elabProposition context.env "∀ n : Nat, n + 0 = n" with
  | .error message => check suite "a well-formed goal elaborates" false message
  | .ok expr =>
      check suite "a well-formed goal elaborates" true
      check suite "an elaborated goal exposes its constants"
        (expr.getUsedConstantsAsSet.contains `HAdd.hAdd)

  match ← elabProposition context.env "∀ (p : Nat) [Fact p.Prime] (a : ZMod p), a ^ p = a" with
  | .error message => check suite "a mathlib goal elaborates" false message
  | .ok expr =>
      check suite "a mathlib goal elaborates" true
      check suite "a mathlib goal resolves mathlib constants"
        (expr.getUsedConstantsAsSet.contains `ZMod)

  -- Without `withoutErrToSorry` this would succeed and rank premises for a proposition built
  -- out of an error, which is worse than failing.
  let unknown ← elabProposition context.env "totally_unknown_identifier"
  check suite "an unknown identifier is an error, not a sorry" unknown.toOption.isNone
    "elaboration succeeded and produced a proposition built out of an error"

  match ← elabProposition context.env "((((" with
  | .ok _ => check suite "an unparseable goal is rejected" false "elaboration succeeded"
  | .error message =>
      check suite "an unparseable goal is rejected" true
      check suite "an unparseable goal says so" (containsSubstring message "parse") message

  match ← elabProposition context.env "42" with
  | .ok _ => check suite "a non-proposition goal is rejected" false "elaboration succeeded"
  | .error message =>
      check suite "a non-proposition goal is rejected" true
      check suite "a non-proposition goal says so"
        (containsSubstring message "not a proposition") message

  match ← elabProposition context.env "   " with
  | .ok _ => check suite "an empty goal is rejected" false "elaboration succeeded"
  | .error _ => check suite "an empty goal is rejected" true

/-! ## Premise ranking -/

def testPremiseRanking (suite : Suite) (context : Context) : IO Unit := do
  let some entry := context.entry? "fermat-units"
    | check suite "fermat-units is in the catalog" false
  let some info := context.find? entry.statement
    | check suite "the fermat-units statement resolves" false
  let some proposition := statementExpr? info
    | check suite "the fermat-units statement denotes a proposition" false
  let (audits, _) ← auditCatalog context
  let excluded := registeredDeclarations context.catalog (dependentClosure audits entry.id)
  let candidates ← rankPremises context proposition excluded 10
  check suite "premise ranking returns candidates" (!candidates.isEmpty)
  check suite "premise ranking excludes the goal's own declaration"
    (!candidates.any (·.name == entry.statement))
  -- The bug this exclusion fixes: without it, the entries built *on* fermat-units dominate
  -- the ranking, and every one of them would make the proof circular.
  check suite "premise ranking excludes circular dependents"
    (!candidates.any (·.name == `FermatFromScratch.pow_card_sub_one_eq_one))
    s!"got {candidates.map (·.name)}"
  check suite "premise ranking is sorted by descending score"
    ((candidates.zip (candidates.extract 1 candidates.size)).all
      fun (left, right) => left.score >= right.score)
  -- IDF weighting is the whole point: a shared `ZMod` has to outrank a shared `Nat`.
  let (frequency, documents) ← context.documentFrequency
  check suite "a specific constant outranks a ubiquitous one"
    (inverseDocumentFrequency frequency documents `ZMod >
     inverseDocumentFrequency frequency documents `Nat)
  -- A ubiquitous constant carries no information either way. Unclamped, its IDF goes slightly
  -- negative and a candidate scores *better* for not mentioning it.
  check suite "inverse document frequency is never negative"
    (inverseDocumentFrequency frequency documents `Eq >= 0.0)

  -- The ranking has to discriminate. Unnormalized overlap is maximized by every candidate
  -- containing all of the goal's constants, so they tie exactly, a large bucket forms at the
  -- top, and `Name.lt` — the alphabet — orders it. "Sorted by descending score" above passes
  -- trivially on such a list, so assert the scores actually differ.
  check suite "premise ranking separates its candidates"
    (candidates.size >= 3 && candidates[0]!.score > candidates[candidates.size - 1]!.score)
    s!"got {candidates.map fun candidate => (candidate.name, candidate.score)}"

  -- End to end, on a goal whose answer is not in dispute. Ranked by unnormalized overlap
  -- `Nat.add_zero` does not appear at all: it ties with every other lemma mentioning ℕ and
  -- addition, and loses the tiebreak to `acc_iff_isEmpty_descending_chain`.
  match ← elabProposition context.env "∀ n : ℕ, n + 0 = n" with
  | .error message => check suite "the add_zero goal elaborates" false message
  | .ok goal =>
      let ranked ← rankPremises context goal {} 3
      check suite "premise ranking puts the obvious lemma in the top three"
        (ranked.any (·.name == `Nat.add_zero))
        s!"got {ranked.map (·.name)}"

/-! ## Search -/

/-! ## Corpus breadth

`search` and `suggest` rank over what is *imported*, not over what exists. When the root module
imported only the mathlib files the catalog's own proofs needed, whole areas of mathematics
resolved to nothing, and an agent asking for premises in one of them got an empty ranking with
no hint that the library was simply absent. `Leanproofs.Library` exists to prevent that; these
are the assertions that notice if it stops working. -/

def testCorpusBreadth (suite : Suite) (context : Context) : IO Unit := do
  -- Namespaces from areas of mathlib that nothing in this repository imports directly. Each
  -- one returned zero hits before the root module imported mathlib in full.
  for namespace_ in #["MeasureTheory", "CategoryTheory", "Complex", "Polynomial", "Topology"] do
    let (_, total) ← searchDeclarations context namespace_ 1 false
    check suite s!"the premise corpus covers {namespace_}" (total > 0)
      "the root module has stopped importing mathlib in full; see Leanproofs/Library.lean"

def testSearch (suite : Suite) (context : Context) : IO Unit := do
  let (hits, total) ← searchDeclarations context "pow_card" 5 false
  check suite "search finds matching theorems" (!hits.isEmpty)
  check suite "search reports a total beyond the truncated page" (total >= hits.size)
  check suite "search respects its limit" (hits.size <= 5)
  -- Ranking has to be by match quality, not hash-map order, or the top of the list is noise.
  check suite "search ranks the exact final component first"
    (hits[0]!.name.toString.endsWith ".pow_card")
    s!"got {hits[0]!.name}"
  check suite "search annotates catalog membership"
    ((← searchDeclarations context "FermatFromScratch.pow_card" 5 false).1.any
      (·.catalogId? == some "fermat-zmod"))

  let (theorems, _) ← searchDeclarations context "Catalan.conjecture" 5 false
  check suite "search omits definitions by default" theorems.isEmpty
  let (all, _) ← searchDeclarations context "Catalan.conjecture" 5 true
  check suite "search includes definitions on request" (!all.isEmpty)

  -- A limit of zero has matches but shows none of them, which is a different answer from
  -- having no matches. The total is what distinguishes them.
  let (none?, stillTotal) ← searchDeclarations context "pow_card" 0 false
  check suite "a zero limit shows no hits" none?.isEmpty
  check suite "a zero limit still reports the true total" (stillTotal > 0)

  let (missing, missingTotal) ← searchDeclarations context "zzz_no_such_declaration" 5 false
  check suite "a query with no matches reports none" missing.isEmpty
  check suite "a query with no matches reports a zero total" (missingTotal == 0)

/-! ## Draft session isolation

`frontier serve` reuses one environment for every request, so `check` has to elaborate against
a *copy*. If a draft's declarations leaked into the session, two agents — or one agent checking
the same file twice — would see results that depend on request order: a later draft resolving a
name it never imported, or a re-check failing because the declaration already exists. -/

def testDraftIsolation (suite : Suite) (context : Context) : IO Unit := do
  let budget := defaultDraftHeartbeats
  let first := "theorem draft_isolated_lemma : (1 : Nat) + 1 = 2 := by decide\n"
  let second := "theorem draft_isolated_user : (1 : Nat) + 1 = 2 := draft_isolated_lemma\n"

  withDraft first fun path => do
    let report ← checkDraft context path budget
    check suite "the first draft in a session is accepted" report.isClean
      s!"fatal: {report.fatal}, diagnostics: {report.diagnostics}"

  withDraft second fun path => do
    let report ← checkDraft context path budget
    check suite "a later draft cannot see an earlier draft's declarations" (!report.isClean)
      "the declaration leaked into the session environment"

  -- Re-checking the same draft must not collide with the first run's declaration.
  withDraft first fun path => do
    let report ← checkDraft context path budget
    check suite "re-checking a draft in the same session still succeeds" report.isClean
      s!"diagnostics: {report.diagnostics}"


end Frontier.Test

