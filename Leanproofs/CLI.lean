/-
Copyright (c) 2026 Jack Michaud. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Michaud
-/

import Lean
import Leanproofs.Registry

/-!
# Frontier CLI

Audits the research catalog against a compiled Lean environment, searches all imported Lean
declarations, and exports a reusable machine-readable theorem index.

This module deliberately does *not* import `Leanproofs.Catalog`. The executable has to import
the project environment at runtime with initializers enabled, and re-initializing modules that
are also statically linked into the binary crashes the process. `Leanproofs.Main` therefore
links only `Lean` and this module, imports the project, and hands the catalog in as data. See
that module for the full explanation.
-/

open Lean

namespace Frontier.CLI

/-! ## Axiom policy

The kernel reports which axioms a proof rests on. Frontier turns that report into a decision.
Anything outside the allowlist is a validation failure, not a footnote, because the roadmap
accepts Lean from automated agents and an unnoticed `native_decide` is a soundness hole. -/

/-- Axioms Frontier accepts. These are the three assumptions of ordinary classical
mathematics as formalized in mathlib. -/
def allowedAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

/-- Axioms that are always rejected, with the reason reported to the author. -/
def deniedAxioms : Array (Name × String) := #[
  (``sorryAx, "the proof is incomplete"),
  (`Lean.ofReduceBool,
    "`native_decide` trusts the Lean compiler and the runtime, which are outside the kernel"),
  (`Lean.ofReduceNat,
    "`native_decide` trusts the Lean compiler and the runtime, which are outside the kernel"),
  (`Lean.trustCompiler, "trusting the compiler places the compiler inside the trust base")
]

def allowedAxiomSet : NameSet :=
  allowedAxioms.foldl (init := {}) NameSet.insert

/-- Why `name` is rejected, if it is.

`native_decide` does not always surface as `Lean.ofReduceBool`: current Lean emits a fresh
per-declaration axiom such as `Foo._native.native_decide.ax_1_1`. The allowlist catches those
either way — which is the reason this is an allowlist and not a denylist — but matching the
shape lets the error say *why* instead of leaving the author to work it out. -/
def deniedAxiomReason? (name : Name) : Option String :=
  match deniedAxioms.find? (·.1 == name) with
  | some (_, reason) => some reason
  | none =>
      let text := name.toString
      if (text.splitOn "native_decide").length > 1 then
        some "`native_decide` trusts the Lean compiler and the runtime, which are outside \
              the kernel; replace it with `decide` or a proof"
      else
        none

/-- Report every policy violation in `axioms`, attributing them to `role`. -/
def axiomPolicyErrors (role : String) (axioms : Array Name) : Array String := Id.run do
  let mut errors := #[]
  for name in axioms do
    if let some reason := deniedAxiomReason? name then
      errors := errors.push s!"{role} depends on the forbidden axiom '{name}': {reason}"
    else if !allowedAxiomSet.contains name then
      errors := errors.push
        s!"{role} depends on '{name}', which is not in the Frontier axiom allowlist \
           ({", ".intercalate (allowedAxioms.map Name.toString).toList}); \
           extend the policy deliberately if this assumption is intended"
  return errors

/-! ## Context -/

/-- Everything a command needs: the imported environment, the catalog loaded from it, and an
index from registered declaration names back to catalog ids. -/
structure Context where
  env : Environment
  catalog : Array Entry
  registered : Std.HashMap Name String

def Context.of (env : Environment) (catalog : Array Entry) : Context :=
  { env, catalog
    registered := catalog.foldl (init := {}) fun map entry =>
      let map := map.insert entry.statement entry.id
      match entry.certificate? with
      | some certificate => map.insert certificate entry.id
      | none => map }

def Context.find? (context : Context) (name : Name) : Option ConstantInfo :=
  context.env.find? name

def Context.entry? (context : Context) (id : String) : Option Entry :=
  context.catalog.find? (·.id == id)

/-! ## Environment traversal -/

/-- Every constant referenced by the type or the value of `name`. -/
def usedConstants (env : Environment) (name : Name) : Array Name :=
  match env.find? name with
  | none => #[]
  | some info =>
      let fromType := info.type.getUsedConstants
      match info.value? (allowOpaque := true) with
      | some value => fromType ++ value.getUsedConstants
      | none => fromType

/-- What one declaration transitively reaches: the axioms it rests on, and the *nearest*
catalog entries above it.

The catalog component stops descending at a registered declaration, so an entry's
dependencies are its minimal catalog ancestors rather than every ancestor. Traversal itself
does not stop, because axioms must still be audited through registered intermediates. -/
structure Reach where
  axioms : NameSet := {}
  catalog : Std.HashSet String := {}
  deriving Inhabited

def Reach.mergeAxioms (target source : Reach) : Reach :=
  { target with
    axioms := source.axioms.toArray.foldl (init := target.axioms) NameSet.insert }

abbrev ReachCache := Std.HashMap Name Reach

/-- Transitive axioms and minimal catalog ancestors of `root`.

The inner traversal is an explicit worklist rather than recursion: mathlib dependency chains
run thousands deep and a recursive walk overflows the stack.

Results are cached, and the walk reuses the cached result of any *registered* declaration it
reaches instead of descending through it again. Registered declarations form a DAG — Lean
forbids circular proofs — so the outer recursion terminates, and a catalog of n entries costs
one walk per entry rather than re-walking every ancestor entry's proof. `visiting` guards the
recursion anyway, so a malformed environment degrades rather than hangs. -/
partial def reachCore (context : Context) (root : Name) (visiting : NameSet) :
    StateM ReachCache Reach := do
  if let some cached := (← get)[root]? then
    return cached
  if visiting.contains root then
    return {}
  let visiting := visiting.insert root
  let mut result : Reach := {}
  if let some (.axiomInfo value) := context.find? root then
    result := { result with axioms := result.axioms.insert value.name }
  let mut seen : NameSet := NameSet.insert {} root
  let mut worklist : Array Name := usedConstants context.env root
  while !worklist.isEmpty do
    let name := worklist.back!
    worklist := worklist.pop
    if seen.contains name then
      continue
    seen := seen.insert name
    match context.registered[name]? with
    | some id =>
        -- Stop the catalog component here: `id` is a minimal registered ancestor. Keep
        -- merging axioms, which must be audited through registered intermediates.
        let sub ← reachCore context name visiting
        let merged := result.mergeAxioms sub
        result := { merged with catalog := merged.catalog.insert id }
    | none =>
        if let some info := context.find? name then
          if let .axiomInfo value := info then
            result := { result with axioms := result.axioms.insert value.name }
          worklist := worklist ++ usedConstants context.env name
  modify (·.insert root result)
  return result

/-- Transitive axioms and minimal catalog ancestors of `root`, threading the shared cache
through whichever monad the caller is working in. -/
def reach {m : Type → Type} [Monad m] (context : Context) (root : Name) :
    StateT ReachCache m Reach := do
  let (result, cache) := (reachCore context root {}).run (← get)
  set cache
  return result

def Reach.axiomArray (reach : Reach) : Array Name :=
  reach.axioms.toArray.qsort Name.lt

def Reach.catalogArray (reach : Reach) (selfId : String) : Array String :=
  (reach.catalog.toList.filter (· != selfId)).toArray.qsort (· < ·)

/-! ## Rendering -/

def declarationKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

/-- The proposition a declaration denotes.

For a theorem or axiom that is its type. For a `def _ : Prop := …` — how open conjectures are
registered — it is the *body*, since the type is just `Prop` and carries no mathematics. -/
def statementExpr? (info : ConstantInfo) : Option Expr :=
  match info with
  | .defnInfo value =>
      if value.type == .sort .zero then some value.value else none
  | .opaqueInfo value =>
      if value.type == .sort .zero then some value.value else none
  | .thmInfo value => some value.type
  | .axiomInfo value => some value.type
  | _ => none

def ppOptions : Options :=
  ({} : Options).setBool `pp.unicode.fun true

def runCoreM {α : Type} (env : Environment) (x : CoreM α) : IO α := do
  let (result, _) ← x.toIO
    { fileName := "<frontier>", fileMap := default, options := ppOptions, maxHeartbeats := 0 }
    { env := env }
  return result

/-- Pretty-print with mathlib notation.

This produces `↑a ^ p = ↑a` rather than `Eq (HPow.hPow …) …` only because `Leanproofs.Main`
imports the environment with `loadExts := true`; without it the delaborators registered by
`notation` are never loaded and every rendered type in the export is unreadable. -/
def prettyExpr (env : Environment) (e : Expr) : IO String := do
  let rendered ← runCoreM env (Meta.MetaM.run' (PrettyPrinter.ppExpr e))
  return Format.pretty rendered 98

def prettyType (env : Environment) (info : ConstantInfo) : IO String :=
  prettyExpr env info.type

/-- Render the proposition a statement declaration denotes, falling back to its type. -/
def prettyStatement (env : Environment) (info : ConstantInfo) : IO String :=
  match statementExpr? info with
  | some proposition => prettyExpr env proposition
  | none => prettyType env info

/-! ## Auditing -/

def certificateShapeIsValid (env : Environment) (entry : Entry)
    (statementInfo certificateInfo : ConstantInfo) : Bool :=
  match statementExpr? statementInfo with
  | none => false
  | some statement =>
      match entry.status with
      | .conditional | .proved | .independent | .undecidable =>
          Kernel.isDefEqGuarded env {} certificateInfo.type statement
      | .disproved =>
          let negated := mkApp (.const ``Not []) statement
          Kernel.isDefEqGuarded env {} certificateInfo.type negated
      | _ => true

def evidenceMatchesStatus (status : Status) (evidence? : Option EvidenceKind) : Bool :=
  match status, evidence? with
  | .formalizing, none | .open, none => true
  | .conditional, some .conditionalProof => true
  | .proved, some .proof => true
  | .disproved, some .counterexample => true
  | .independent, some .modelConstruction | .independent, some .metatheorem => true
  | .undecidable, some .reduction | .undecidable, some .metatheorem => true
  | _, _ => false

/-- A `status`/`literature` pair that cannot both be true. -/
def literatureContradiction (status : Status) (literature : Literature) : Option String :=
  match status, literature with
  | .proved, .disproved =>
      some "this repository proves the statement while the literature field says it is refuted"
  | .disproved, .proved =>
      some "this repository refutes the statement while the literature field says it is proved"
  | _, _ => none

structure SanityCheck where
  name : Name
  type : String
  deriving Inhabited

structure Audit where
  entry : Entry
  statementType : String
  statementAxioms : Array String
  certificateType? : Option String
  declarationKind : String
  dependencies : Array String
  axioms : Array String
  sanityChecks : Array SanityCheck
  errors : Array String

def Audit.isValid (audit : Audit) : Bool := audit.errors.isEmpty

def auditEntry (context : Context) (entry : Entry) : StateT ReachCache IO Audit := do
  let env := context.env
  let mut errors := #[]
  let mut statementType := "<missing>"
  let mut kind := "missing"
  let mut statementAxioms : Array Name := #[]
  -- Statement.
  let statementInfo? := context.find? entry.statement
  match statementInfo? with
  | none =>
      errors := errors.push s!"statement declaration '{entry.statement}' does not exist"
  | some info =>
      statementType ← prettyStatement env info
      kind := declarationKind info
      if (statementExpr? info).isNone then
        errors := errors.push
          s!"statement declaration '{entry.statement}' does not denote a proposition"
      -- A statement built out of `sorry` would make an `open` entry look clean, so audit it
      -- even when there is no certificate to audit.
      let statementReach ← reach context entry.statement
      statementAxioms := statementReach.axiomArray
      errors := errors ++ axiomPolicyErrors "the statement" statementAxioms
  -- Certificate.
  let mut certificateType? := none
  let mut axiomNames : Array Name := #[]
  let mut dependencies : Array String := #[]
  match entry.certificate? with
  | none =>
      if entry.status.isClosed then
        errors := errors.push s!"closed status '{entry.status.toString}' requires a certificate"
      if entry.evidence?.isSome then
        errors := errors.push "an evidence kind requires a certificate"
  | some certificate =>
      match context.find? certificate with
      | none =>
          errors := errors.push s!"certificate declaration '{certificate}' does not exist"
      | some certificateInfo =>
          certificateType? := some (← prettyType env certificateInfo)
          if !entry.status.isClosed then
            errors := errors.push
              s!"status '{entry.status.toString}' cannot have a closing certificate"
          match certificateInfo with
          | .thmInfo _ => pure ()
          | _ => errors := errors.push s!"certificate '{certificate}' is not a Lean theorem"
          if let some statementInfo := statementInfo? then
            if !certificateShapeIsValid env entry statementInfo certificateInfo then
              errors := errors.push
                s!"certificate type does not match the '{entry.status.toString}' claim"
          let certificateReach ← reach context certificate
          axiomNames := certificateReach.axiomArray
          dependencies := certificateReach.catalogArray entry.id
          errors := errors ++ axiomPolicyErrors s!"certificate '{certificate}'" axiomNames
  -- Entries with no certificate take their dependencies from the statement.
  if entry.certificate?.isNone && statementInfo?.isSome then
    dependencies := (← reach context entry.statement).catalogArray entry.id
  -- Sanity checks.
  let mut sanityChecks : Array SanityCheck := #[]
  for name in entry.sanityChecks do
    match context.find? name with
    | none => errors := errors.push s!"sanity check '{name}' does not exist"
    | some info =>
        match info with
        | .thmInfo _ => pure ()
        | _ => errors := errors.push s!"sanity check '{name}' is not a Lean theorem"
        let checkReach ← reach context name
        errors := errors ++ axiomPolicyErrors s!"sanity check '{name}'" checkReach.axiomArray
        sanityChecks := sanityChecks.push { name, type := (← prettyType env info) }
  if !entry.status.isClosed && entry.sanityChecks.isEmpty then
    errors := errors.push
      "an unresolved entry needs at least one sanity check; a formal statement nothing has \
       been proved about is exactly where mis-formalization hides (see docs/adding-results.md)"
  -- Metadata.
  if entry.id.trimAscii.isEmpty then
    errors := errors.push "entry id cannot be empty"
  if entry.title.trimAscii.isEmpty then
    errors := errors.push "entry title cannot be empty"
  if entry.evidence?.isNone && entry.certificate?.isSome then
    errors := errors.push "a certificate requires an evidence kind"
  if !evidenceMatchesStatus entry.status entry.evidence? then
    let evidence := entry.evidence?.map EvidenceKind.toString |>.getD "none"
    errors := errors.push
      s!"evidence '{evidence}' is incompatible with status '{entry.status.toString}'"
  if entry.status.isRelative && (entry.baseTheory?.getD "").trimAscii.isEmpty then
    errors := errors.push
      s!"status '{entry.status.toString}' is relative and must name the formalized base theory \
         or decision problem in `baseTheory?`"
  if entry.literature.requiresCitation && (entry.citation?.getD "").trimAscii.isEmpty then
    errors := errors.push
      s!"literature state '{entry.literature.toString}' makes a claim about existing \
         mathematics and requires a citation"
  if let some contradiction := literatureContradiction entry.status entry.literature then
    errors := errors.push contradiction
  if !isIsoDate entry.created then
    errors := errors.push s!"created '{entry.created}' is not an ISO-8601 YYYY-MM-DD date"
  if !isIsoDate entry.updated then
    errors := errors.push s!"updated '{entry.updated}' is not an ISO-8601 YYYY-MM-DD date"
  if entry.authors.isEmpty then
    errors := errors.push "every entry needs at least one human author"
  return {
    entry
    statementType
    statementAxioms := statementAxioms.map (·.toString)
    certificateType?
    declarationKind := kind
    dependencies
    axioms := axiomNames.map (·.toString)
    sanityChecks
    errors
  }

def duplicateIdErrors (catalog : Array Entry) : Array String := Id.run do
  let mut seen : Std.HashSet String := {}
  let mut errors := #[]
  for entry in catalog do
    if seen.contains entry.id then
      errors := errors.push s!"duplicate entry id '{entry.id}'"
    seen := seen.insert entry.id
  return errors

def auditCatalog (context : Context) : IO (Array Audit × Array String) := do
  let (audits, _) ← (context.catalog.mapM (auditEntry context)).run {}
  return (audits, duplicateIdErrors context.catalog)

/-! ## Export -/

def optionStringJson : Option String → Json
  | some value => toJson value
  | none => Json.null

def entryJson (audit : Audit) : Json :=
  Json.mkObj [
    ("id", toJson audit.entry.id),
    ("title", toJson audit.entry.title),
    ("summary", toJson audit.entry.summary),
    ("status", toJson audit.entry.status.toString),
    ("literature", toJson audit.entry.literature.toString),
    ("citation", optionStringJson audit.entry.citation?),
    ("topic", toJson audit.entry.topic),
    ("tags", toJson audit.entry.tags),
    ("statement", toJson audit.entry.statement.toString),
    ("statementType", toJson audit.statementType),
    ("statementAxioms", toJson audit.statementAxioms),
    ("declarationKind", toJson audit.declarationKind),
    ("certificate", optionStringJson (audit.entry.certificate?.map (·.toString))),
    ("certificateType", optionStringJson audit.certificateType?),
    ("evidence", optionStringJson (audit.entry.evidence?.map EvidenceKind.toString)),
    ("baseTheory", optionStringJson audit.entry.baseTheory?),
    ("sanityChecks", Json.arr (audit.sanityChecks.map fun check =>
      Json.mkObj [("name", toJson check.name.toString), ("type", toJson check.type)])),
    ("dependencies", toJson audit.dependencies),
    ("axioms", toJson audit.axioms),
    ("authors", toJson audit.entry.authors),
    ("tooling", toJson audit.entry.tooling),
    ("source", optionStringJson audit.entry.source?),
    ("created", toJson audit.entry.created),
    ("updated", toJson audit.entry.updated),
    ("valid", toJson audit.isValid),
    ("errors", toJson audit.errors)
  ]

def catalogJson (audits : Array Audit) (globalErrors : Array String) : Json :=
  let count (predicate : Audit → Bool) : Nat :=
    audits.foldl (init := 0) fun total audit => if predicate audit then total + 1 else total
  Json.mkObj [
    ("schemaVersion", toJson (2 : Nat)),
    ("project", toJson "Frontier"),
    ("axiomPolicy", Json.mkObj [
      ("allowed", toJson (allowedAxioms.map Name.toString)),
      ("denied", toJson (deniedAxioms.map (·.1.toString)))
    ]),
    ("summary", Json.mkObj [
      ("total", toJson audits.size),
      ("valid", toJson (count Audit.isValid)),
      ("closed", toJson (count (·.entry.status.isClosed))),
      ("literatureUnresolved", toJson (count (·.entry.literature == .unresolved))),
      ("globalErrors", toJson globalErrors)
    ]),
    ("entries", Json.arr (audits.map entryJson))
  ]

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

/-- Inverse document frequency of a constant, in a corpus of `documents` theorems. -/
def inverseDocumentFrequency (frequency : Std.HashMap Name Nat) (documents : Nat)
    (name : Name) : Float :=
  let observed := frequency.getD name 0
  Float.log (documents.toFloat / (1.0 + observed.toFloat))

def formatScore (score : Float) : String :=
  let scaled := (score * 100.0).round.toUInt64.toNat
  s!"{scaled / 100}.{if scaled % 100 < 10 then "0" else ""}{scaled % 100}"

/-! ## Commands -/

def printEntry (audit : Audit) : IO Unit := do
  IO.println s!"{audit.entry.title} [{audit.entry.status.toString}]"
  IO.println s!"id:           {audit.entry.id}"
  IO.println s!"topic:        {audit.entry.topic}"
  IO.println s!"literature:   {audit.entry.literature.toString}"
  if let some citation := audit.entry.citation? then
    IO.println s!"citation:     {citation}"
  IO.println s!"statement:    {audit.entry.statement}"
  IO.println s!"proposition:  {audit.statementType}"
  if let some certificate := audit.entry.certificate? then
    IO.println s!"certificate:  {certificate}"
  if let some evidence := audit.entry.evidence? then
    IO.println s!"evidence:     {evidence.toString}"
  if let some baseTheory := audit.entry.baseTheory? then
    IO.println s!"base theory:  {baseTheory}"
  IO.println s!"tags:         {", ".intercalate audit.entry.tags.toList}"
  let orNone (values : Array String) : String :=
    if values.isEmpty then "none" else ", ".intercalate values.toList
  IO.println s!"depends on:   {orNone audit.dependencies}"
  IO.println s!"axioms:       {orNone audit.axioms}"
  if !audit.sanityChecks.isEmpty then
    IO.println "sanity checks:"
    for check in audit.sanityChecks do
      IO.println s!"  {check.name} : {check.type}"
  IO.println s!"summary:      {audit.entry.summary}"
  if !audit.errors.isEmpty then
    for error in audit.errors do
      IO.eprintln s!"error: {error}"

def runValidate (context : Context) : IO UInt32 := do
  let (audits, globalErrors) ← auditCatalog context
  let mut invalid := 0
  for audit in audits do
    if audit.isValid then
      IO.println s!"ok  {audit.entry.id} ({audit.entry.status.toString}, \
        literature: {audit.entry.literature.toString})"
    else
      invalid := invalid + 1
      IO.eprintln s!"ERR {audit.entry.id}"
      for error in audit.errors do
        IO.eprintln s!"    {error}"
  for error in globalErrors do
    IO.eprintln s!"ERR {error}"
  -- Count entries and catalog-wide errors separately. Folding the global errors into the
  -- entry tally reports a smaller number of passing entries than actually passed.
  IO.println s!"\n{audits.size - invalid}/{audits.size} registry entries passed"
  if !globalErrors.isEmpty then
    IO.println s!"{globalErrors.size} catalog-wide error(s)"
  return if invalid == 0 && globalErrors.isEmpty then 0 else 1

def runList (context : Context) (query? : Option String) : IO UInt32 := do
  let (audits, _) ← auditCatalog context
  for audit in audits do
    let tags := " ".intercalate audit.entry.tags.toList
    let searchable :=
      s!"{audit.entry.id} {audit.entry.title} {audit.entry.topic} {tags}".toLower
    if query?.all (fun query => containsSubstring searchable query.toLower) then
      IO.println s!"{audit.entry.id}\t{audit.entry.status.toString}\t\
        {audit.entry.literature.toString}\t{audit.entry.title}"
  return 0

def runShow (context : Context) (id : String) : IO UInt32 := do
  let some entry := context.entry? id | do
    IO.eprintln s!"unknown registry id '{id}'"
    return 1
  let (audit, _) ← (auditEntry context entry).run {}
  printEntry audit
  return 0

/-- Name search over every imported declaration.

Every match is collected before truncation and the result is ordered by match quality, so the
output is a stable, meaningful top `limit` rather than whichever entries the hash map happened
to yield first. -/
def runSearch (context : Context) (query : String) (limit : Nat := 25) : IO UInt32 := do
  if query.trimAscii.isEmpty then
    IO.eprintln "search requires a non-empty query"
    return 1
  let lowered := query.toLower
  let hits : Array (Nat × Nat × Name) :=
    context.env.constants.fold (init := #[]) fun results name info =>
      match info with
      | .thmInfo _ | .axiomInfo _ =>
          if name.isInternal then results
          else
            match searchRank lowered name.toString with
            | some rank => results.push (rank, name.toString.length, name)
            | none => results
      | _ => results
  let ranked := hits.qsort fun left right =>
    if left.1 != right.1 then left.1 < right.1
    else if left.2.1 != right.2.1 then left.2.1 < right.2.1
    else Name.lt left.2.2 right.2.2
  if ranked.isEmpty then
    IO.println s!"No imported theorem names matched '{query}'."
    return 0
  for (_, _, name) in ranked.take limit do
    if let some info := context.find? name then
      IO.println s!"{name} : {← prettyType context.env info}"
  if ranked.size > limit then
    IO.println s!"\n… {ranked.size - limit} further matches not shown."
  return 0

/-- Rank imported theorems as candidate premises for a registered statement.

Scoring is inverse-document-frequency-weighted overlap of the constants appearing in the two
propositions, so a shared `ZMod` counts for far more than a shared `Nat`. This is a ranking
heuristic only: a premise becomes part of a proof when Lean accepts it, not before. -/
def runSuggest (context : Context) (id : String) (limit : Nat := 15) : IO UInt32 := do
  let some entry := context.entry? id | do
    IO.eprintln s!"unknown registry id '{id}'"
    return 1
  let some statementInfo := context.find? entry.statement | do
    IO.eprintln s!"statement declaration '{entry.statement}' does not exist"
    return 1
  -- Use the denoted proposition, not the declaration type: for a `def _ : Prop` the type is
  -- just `Prop` and shares no constants with anything, which silently returns no candidates.
  let some proposition := statementExpr? statementInfo | do
    IO.eprintln s!"statement declaration '{entry.statement}' does not denote a proposition"
    return 1
  let target := proposition.getUsedConstantsAsSet
  let (frequency, documents) := constantDocumentFrequency context.env
  -- The entry's own declarations are not candidate premises for itself. Sanity checks in
  -- particular share every constant with the statement, so they would otherwise monopolize
  -- the top of the ranking while telling the author nothing new.
  let excluded : NameSet :=
    (#[entry.statement] ++ entry.certificate?.toArray ++ entry.sanityChecks).foldl
      (init := {}) NameSet.insert
  let scored : Array (Float × Name) :=
    context.env.constants.fold (init := #[]) fun results name info =>
      match info with
      | .thmInfo _ =>
          if name.isInternal || excluded.contains name
              || context.registered[name]?.any (· == entry.id) then
            results
          else
            let candidate := info.type.getUsedConstantsAsSet
            let score := target.toArray.foldl (init := 0.0) fun total constant =>
              if candidate.contains constant then
                total + inverseDocumentFrequency frequency documents constant
              else total
            if score > 0.0 then results.push (score, name) else results
      | _ => results
  let ranked := scored.qsort fun left right =>
    if left.1 != right.1 then left.1 > right.1 else Name.lt left.2 right.2
  IO.println s!"Reusable theorem candidates for {entry.title}:"
  if ranked.isEmpty then
    IO.println "No candidates shared statement constants."
    return 0
  for (score, name) in ranked.take limit do
    if let some info := context.find? name then
      IO.println s!"[{formatScore score}] {name} : {← prettyType context.env info}"
  return 0

def runGraph (context : Context) : IO UInt32 := do
  let (audits, _) ← auditCatalog context
  IO.println "flowchart LR"
  for audit in audits do
    IO.println s!"  {audit.entry.id.replace "-" "_"}[\"{audit.entry.title}\"]"
  for audit in audits do
    for dependency in audit.dependencies do
      IO.println s!"  {dependency.replace "-" "_"} --> {audit.entry.id.replace "-" "_"}"
  return 0

def runExport (context : Context) (path : System.FilePath) : IO UInt32 := do
  let (audits, globalErrors) ← auditCatalog context
  let json := catalogJson audits globalErrors
  if let some parent := path.parent then
    IO.FS.createDirAll parent
  IO.FS.writeFile path (json.pretty 120)
  IO.println s!"Exported {audits.size} entries to {path}"
  return if globalErrors.isEmpty && audits.all Audit.isValid then 0 else 1

def runPolicy : IO UInt32 := do
  IO.println "Frontier axiom policy\n"
  IO.println "allowed:"
  for name in allowedAxioms do
    IO.println s!"  {name}"
  IO.println "\ndenied:"
  for (name, reason) in deniedAxioms do
    IO.println s!"  {name}: {reason}"
  IO.println "\nAny other axiom reaching a statement, certificate, or sanity check is a \
    validation error."
  return 0

def printHelp : IO Unit :=
  IO.println "Frontier: a Lean-checked mathematical research registry\n\n\
    Usage:\n\
      lake exe frontier validate\n\
      lake exe frontier list [query]\n\
      lake exe frontier show <id>\n\
      lake exe frontier search <Lean declaration name>\n\
      lake exe frontier suggest <registry id>\n\
      lake exe frontier graph\n\
      lake exe frontier policy\n\
      lake exe frontier export [path]\n\n\
    The default export path is build/frontier.json."

/-- Commands that answer without importing the project environment, which costs several
seconds. -/
def runWithoutEnvironment? (args : List String) : Option (IO UInt32) :=
  match args with
  | ["help"] | ["--help"] | ["-h"] | [] => some (printHelp *> pure 0)
  | ["policy"] => some runPolicy
  | _ => none

def run (context : Context) (args : List String) : IO UInt32 := do
  match args with
  | [] => printHelp *> pure 0
  | command :: rest =>
      match command, rest with
      | "validate", [] => runValidate context
      | "list", [] => runList context none
      | "list", query => runList context (some (" ".intercalate query))
      | "show", [id] => runShow context id
      | "search", [] => IO.eprintln "search requires a query" *> pure 1
      | "search", query => runSearch context (" ".intercalate query)
      | "suggest", [id] => runSuggest context id
      | "graph", [] => runGraph context
      | "export", [] => runExport context "build/frontier.json"
      | "export", [path] => runExport context path
      | _, _ => IO.eprintln s!"invalid command or arguments: {command}" *> printHelp *> pure 1

end Frontier.CLI
