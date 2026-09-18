/-
Copyright (c) 2026 Jack Michaud. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Michaud
-/

import Leanproofs.Frontier.Core
import Leanproofs.Frontier.Audit

open Lean

namespace Frontier.CLI

/-! ## Search and premise ranking -/

def containsSubstring (haystack needle : String) : Bool :=
  needle.isEmpty || (haystack.splitOn needle).length > 1

/-- Rank a name against a query: exact, final component, prefix, then substring. -/
def searchRank (query name : String) : Option Nat :=
  let lower := name.toLower
  if lower == query then some 0
  else if lower.endsWith ("." ++ query) then some 1
  else if lower.startsWith query then some 2
  else if containsSubstring lower query then some 3
  else none

/-- Documents in which each constant appears, over the types of all imported theorems.

This is the corpus statistic behind inverse document frequency: `Nat` and `Membership` appear
almost everywhere and carry no signal, while `ZMod` or `Nat.Prime` do. -/
def constantDocumentFrequency (env : Environment) : Std.HashMap Name Nat × Nat :=
  env.constants.fold (init := ({}, 0)) fun (frequency, documents) _ info =>
    match info with
    | .thmInfo _ =>
        let constants := info.type.getUsedConstantsAsSet
        let frequency := constants.toArray.foldl (init := frequency) fun map name =>
          map.insert name (map.getD name 0 + 1)
        (frequency, documents + 1)
    | _ => (frequency, documents)

/-- Inverse document frequency of a constant, in a corpus of `documents` theorems.

Clamped below at zero. A constant appearing in almost every theorem sends the unclamped
logarithm slightly negative, which would score a candidate *better* for failing to mention
`Eq` — a sign flip on the one term that carries no information either way. -/
def inverseDocumentFrequency (frequency : Std.HashMap Name Nat) (documents : Nat)
    (name : Name) : Float :=
  let observed := frequency.getD name 0
  let weight := Float.log (documents.toFloat / (1.0 + observed.toFloat))
  if weight < 0.0 then 0.0 else weight

def formatScore (score : Float) : String :=
  let scaled := (score * 100.0).round.toUInt64.toNat
  s!"{scaled / 100}.{if scaled % 100 < 10 then "0" else ""}{scaled % 100}"

/-- A score as a JSON number with two decimal places. There is no `ToJson Float`, and emitting
the score as a string would force every consumer to parse it back before sorting. -/
def scoreJson (score : Float) : Json :=
  Json.num ⟨(score * 100.0).round.toUInt64.toNat, 2⟩

/-! ### What a proposition is about

Overlap over *every* constant in a statement treats a theorem that happens to mention `ℕ` in a
side condition the same as one whose conclusion is the shape being proved. The conclusion is
where the content is, so it is weighted separately. -/

/-- The conclusion of a proposition: whatever is left under its `∀` and `→` binders. -/
partial def conclusionOf : Expr → Expr
  | .forallE _ _ body _ => conclusionOf body
  | .mdata _ body => conclusionOf body
  | proposition => proposition

/-- Constants identifying what a proposition concludes: the head of its conclusion together
with the heads of that conclusion's arguments.

The head alone discriminates nothing — nearly every theorem in mathlib concludes in `Eq` or
`Iff`. One level down is where the signal is: `add_zero` and the goal `∀ n : ℕ, n + 0 = n`
agree on `HAdd.hAdd`, while a lemma that merely mentions `ℕ` somewhere in a hypothesis does
not. -/
def conclusionKeys (proposition : Expr) : NameSet := Id.run do
  let target := conclusionOf proposition
  let mut keys : NameSet := {}
  if let some head := target.getAppFn.constName? then
    keys := keys.insert head
  for argument in target.getAppArgs do
    if let some head := argument.getAppFn.constName? then
      keys := keys.insert head
  return keys

/-- Total inverse document frequency of `names`. -/
def idfMass (idf : Name → Float) (names : Array Name) : Float :=
  names.foldl (init := 0.0) fun total name => total + idf name

/-- Total inverse document frequency of the constants two arrays share.

Both arguments come from `NameSet.toArray` and therefore carry the same `Name.quickCmp` order,
so a linear merge answers what would otherwise be a membership test per element. Premise
ranking runs this against every imported theorem, so the constant factor is the whole cost of
the command. -/
def idfOverlap (idf : Name → Float) (left right : Array Name) : Float := Id.run do
  let mut total := 0.0
  let mut i := 0
  let mut j := 0
  while i < left.size && j < right.size do
    match Name.quickCmp left[i]! right[j]! with
    | .lt => i := i + 1
    | .gt => j := j + 1
    | .eq =>
        total := total + idf left[i]!
        i := i + 1
        j := j + 1
  return total

/-- How much a conclusion-to-conclusion match counts relative to a match anywhere in the
statement. -/
def conclusionKeyWeight : Float := 2.0

/-- Prepare every imported theorem for ranking.

Two passes over the environment: document frequency is a corpus statistic, so no theorem's
mass is known until every theorem has been read. -/
def buildPremiseIndex (env : Environment) : PremiseIndex :=
  let (frequency, documents) := constantDocumentFrequency env
  let idf := inverseDocumentFrequency frequency documents
  let premises := env.constants.fold (init := #[]) fun premises name info =>
    match info with
    | .thmInfo value =>
        if name.isInternal then premises
        else
          let constants := value.type.getUsedConstantsAsSet.toArray
          premises.push {
            name, constants
            keys := (conclusionKeys value.type).toArray
            mass := idfMass idf constants }
    | _ => premises
  { premises, frequency, documents }

/-- The prepared corpus, built on first use and reused for the rest of the session. -/
def Context.premiseIndex (context : Context) : IO PremiseIndex := do
  if let some cached ← context.premiseIndexRef.get then
    return cached
  let computed := buildPremiseIndex context.env
  context.premiseIndexRef.set (some computed)
  return computed

/-- Corpus statistics alone, for callers that need the weighting rather than the corpus. -/
def Context.documentFrequency (context : Context) : IO (Std.HashMap Name Nat × Nat) := do
  let index ← context.premiseIndex
  return (index.frequency, index.documents)

/-- One declaration matching a search. -/
structure SearchHit where
  name : Name
  kind : String
  type : String
  /-- The catalog entry registering this declaration, if it is a Frontier result. -/
  catalogId? : Option String
  deriving Inhabited

def defaultSearchLimit : Nat := 25

/-- Name search over every imported declaration.

Every match is collected before truncation and the result is ordered by match quality, so the
output is a stable, meaningful top `limit` rather than whichever entries the hash map happened
to yield first. Returns the truncated hits together with the total number of matches.

Theorems and axioms are searched by default. `includeDefinitions` widens that to definitions
and inductives, which matters when the thing being looked for is a *definition* to state a
goal in terms of rather than a lemma to apply. -/
def searchDeclarations (context : Context) (query : String) (limit : Nat)
    (includeDefinitions : Bool) : IO (Array SearchHit × Nat) := do
  let lowered := query.toLower
  let admissible (info : ConstantInfo) : Bool :=
    match info with
    | .thmInfo _ | .axiomInfo _ => true
    | .defnInfo _ | .inductInfo _ | .opaqueInfo _ => includeDefinitions
    | _ => false
  let candidates : Array (Nat × Nat × Name) :=
    context.env.constants.fold (init := #[]) fun results name info =>
      if !admissible info || name.isInternal then results
      else
        match searchRank lowered name.toString with
        | some rank => results.push (rank, name.toString.length, name)
        | none => results
  let ranked := candidates.qsort fun left right =>
    if left.1 != right.1 then left.1 < right.1
    else if left.2.1 != right.2.1 then left.2.1 < right.2.1
    else Name.lt left.2.2 right.2.2
  let mut hits := #[]
  for (_, _, name) in ranked.take limit do
    if let some info := context.find? name then
      hits := hits.push {
        name
        kind := declarationKind info
        type := ← prettyType context.env info
        catalogId? := context.registered[name]?
      }
  return (hits, ranked.size)

/-- A theorem ranked as a candidate premise for a goal. -/
structure PremiseCandidate where
  score : Float
  name : Name
  type : String
  catalogId? : Option String
  deriving Inhabited

def defaultSuggestLimit : Nat := 15

/-- Rank imported theorems as candidate premises for a goal.

Scoring is cosine-style inverse-document-frequency-weighted overlap between the two
propositions, with conclusions weighted above hypotheses. Three terms:

* **Overlap.** IDF-weighted constants the goal and the candidate share, so a shared `ZMod`
  counts for far more than a shared `Nat`.
* **Conclusion match.** The same, over `conclusionKeys` only, added again at
  `conclusionKeyWeight`. Concluding in the shape being proved is worth more than mentioning it.
* **Normalization** by the square root of the candidate's own IDF mass. This is the term that
  makes the ranking a ranking. Unnormalized overlap is bounded above by the goal's total mass
  and *attains* that bound for every candidate containing all of the goal's constants, so a
  large tied bucket forms at the top and `Name.lt` — the alphabet — orders it. Dividing by the
  candidate's mass breaks the tie in the right direction too: between two theorems that both
  cover the goal, the one that drags in less unrelated material is the better premise.

This is a ranking heuristic only: a premise becomes part of a proof when Lean accepts it, not
before. -/
def rankPremises (context : Context) (goal : Expr) (excluded : NameSet) (limit : Nat) :
    IO (Array PremiseCandidate) := do
  let target := goal.getUsedConstantsAsSet.toArray
  let targetKeys := (conclusionKeys goal).toArray
  let index ← context.premiseIndex
  let idf := inverseDocumentFrequency index.frequency index.documents
  let scored : Array (Float × Name) :=
    index.premises.foldl (init := #[]) fun results premise =>
      if excluded.contains premise.name then results
      else
        let shared := idfOverlap idf target premise.constants
        if shared <= 0.0 then results
        else
          let concluded := idfOverlap idf targetKeys premise.keys
          -- Floored at one so a candidate built entirely from ubiquitous constants cannot
          -- divide its way to the top on a near-zero denominator.
          let normalizer := Float.sqrt (if premise.mass < 1.0 then 1.0 else premise.mass)
          results.push ((shared + conclusionKeyWeight * concluded) / normalizer, premise.name)
  let ranked := scored.qsort fun left right =>
    if left.1 != right.1 then left.1 > right.1 else Name.lt left.2 right.2
  let mut candidates := #[]
  for (score, name) in ranked.take limit do
    if let some info := context.find? name then
      candidates := candidates.push {
        score
        name
        type := ← prettyType context.env info
        catalogId? := context.registered[name]?
      }
  return candidates

/-- Catalog ids that transitively depend on `id`, including `id` itself.

No declaration belonging to one of these entries can be a premise for `id`: using it would
make the proof circular. Recorded edges are *minimal* ancestors, so reaching every dependent
requires closing them transitively — without this, `suggest` for a lemma cheerfully proposes
the theorems built on top of it, which are the one set of candidates guaranteed to be
useless. -/
def dependentClosure (audits : Array Audit) (id : String) : Std.HashSet String := Id.run do
  let mut closure : Std.HashSet String := ({} : Std.HashSet String).insert id
  let mut changed := true
  while changed do
    changed := false
    for audit in audits do
      if !closure.contains audit.entry.id && audit.dependencies.any closure.contains then
        closure := closure.insert audit.entry.id
        changed := true
  return closure

/-- Every declaration registered by an entry in `ids`, including sanity checks.

Sanity checks matter here: they share every constant with their statement, so leaving them in
lets them monopolize the top of a ranking while telling the author nothing. -/
def registeredDeclarations (catalog : Array Entry) (ids : Std.HashSet String) : NameSet :=
  catalog.foldl (init := {}) fun names entry =>
    if ids.contains entry.id then
      (#[entry.statement] ++ entry.certificate?.toArray ++ entry.sanityChecks).foldl
        (init := names) NameSet.insert
    else names

end Frontier.CLI
