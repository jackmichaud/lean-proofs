/-
Copyright (c) 2026 Jack Michaud. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Michaud
-/

import Lean
import Leanproofs.Catalog

/-!
# Frontier CLI

Audits the research catalog against a compiled Lean environment, searches all imported Lean
declarations, and exports a reusable machine-readable theorem index.
-/

open Lean

namespace Frontier.CLI

structure WalkState where
  seen : NameSet := {}
  axioms : NameSet := {}

partial def visitDeclaration (env : Environment) (name : Name) : StateM WalkState Unit := do
  let state ← get
  if state.seen.contains name then
    return
  modify fun s => { s with seen := s.seen.insert name }
  let some info := env.find? name | return
  match info with
  | .axiomInfo value =>
      modify fun s => { s with axioms := s.axioms.insert value.name }
      for dependency in value.type.getUsedConstants do
        visitDeclaration env dependency
  | _ =>
      for dependency in info.type.getUsedConstants do
        visitDeclaration env dependency
      if let some value := info.value? (allowOpaque := true) then
        for dependency in value.getUsedConstants do
          visitDeclaration env dependency

def collectAxioms (env : Environment) (name : Name) : Array Name :=
  let state := ((visitDeclaration env name).run {}).2
  state.axioms.toArray.qsort Name.lt

def declarationConstants (env : Environment) (name : Name) : NameSet :=
  match env.find? name with
  | none => {}
  | some info => info.getUsedConstantsAsSet

def declarationKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def statementExpr? (info : ConstantInfo) : Option Expr :=
  match info with
  | .defnInfo value =>
      if value.type == .sort .zero then some value.value else none
  | .opaqueInfo value =>
      if value.type == .sort .zero then some value.value else none
  | .thmInfo value => some value.type
  | .axiomInfo value => some value.type
  | _ => none

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

def prettyType (env : Environment) (info : ConstantInfo) : IO String := do
  let rendered ← PrettyPrinter.ppExprLegacy env {} {} {} info.type
  return toString rendered

def directCatalogDependencies (env : Environment) (entry : Entry) : Array String :=
  let root := entry.certificate?.getD entry.statement
  let used := declarationConstants env root
  catalog.filterMap fun candidate =>
    if candidate.id == entry.id then none
    else
      let names := #[candidate.statement] ++ candidate.certificate?.toArray
      if names.any used.contains then some candidate.id else none

structure Audit where
  entry : Entry
  statementType : String
  certificateType? : Option String
  declarationKind : String
  dependencies : Array String
  axioms : Array String
  errors : Array String

def Audit.isValid (audit : Audit) : Bool := audit.errors.isEmpty

def auditEntry (env : Environment) (entry : Entry) : IO Audit := do
  let mut errors := #[]
  let mut statementType := "<missing>"
  let mut kind := "missing"
  let statementInfo? := env.find? entry.statement
  match statementInfo? with
  | none =>
      errors := errors.push s!"statement declaration '{entry.statement}' does not exist"
  | some info =>
      statementType ← prettyType env info
      kind := declarationKind info
      if (statementExpr? info).isNone then
        errors := errors.push
          s!"statement declaration '{entry.statement}' does not denote a proposition"
  let mut certificateType? := none
  let mut axiomNames : Array Name := #[]
  match entry.certificate? with
  | none =>
      if entry.status.isClosed then
        errors := errors.push s!"closed status '{entry.status.toString}' requires a certificate"
      if entry.evidence?.isSome then
        errors := errors.push "an evidence kind requires a certificate"
  | some certificate =>
      match env.find? certificate with
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
          axiomNames := collectAxioms env certificate
          if axiomNames.contains ``sorryAx then
            errors := errors.push s!"certificate '{certificate}' transitively depends on sorryAx"
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
  return {
    entry
    statementType
    certificateType?
    declarationKind := kind
    dependencies := directCatalogDependencies env entry
    axioms := axiomNames.map (·.toString)
    errors
  }

def duplicateIdErrors : Array String := Id.run do
  let mut seen : Std.HashSet String := {}
  let mut errors := #[]
  for entry in catalog do
    if seen.contains entry.id then
      errors := errors.push s!"duplicate entry id '{entry.id}'"
    seen := seen.insert entry.id
  return errors

def auditCatalog (env : Environment) : IO (Array Audit × Array String) := do
  return (← catalog.mapM (auditEntry env), duplicateIdErrors)

def optionStringJson : Option String → Json
  | some value => toJson value
  | none => Json.null

def entryJson (audit : Audit) : Json :=
  Json.mkObj [
    ("id", toJson audit.entry.id),
    ("title", toJson audit.entry.title),
    ("summary", toJson audit.entry.summary),
    ("status", toJson audit.entry.status.toString),
    ("topic", toJson audit.entry.topic),
    ("tags", toJson audit.entry.tags),
    ("statement", toJson audit.entry.statement.toString),
    ("statementType", toJson audit.statementType),
    ("declarationKind", toJson audit.declarationKind),
    ("certificate", optionStringJson (audit.entry.certificate?.map (·.toString))),
    ("certificateType", optionStringJson audit.certificateType?),
    ("evidence", optionStringJson (audit.entry.evidence?.map EvidenceKind.toString)),
    ("dependencies", toJson audit.dependencies),
    ("axioms", toJson audit.axioms),
    ("authors", toJson audit.entry.authors),
    ("source", optionStringJson audit.entry.source?),
    ("created", toJson audit.entry.created),
    ("updated", toJson audit.entry.updated),
    ("valid", toJson audit.isValid),
    ("errors", toJson audit.errors)
  ]

def catalogJson (audits : Array Audit) (globalErrors : Array String) : Json :=
  let validCount := audits.foldl (init := 0) fun count audit =>
    if audit.isValid then count + 1 else count
  let closedCount := audits.foldl (init := 0) fun count audit =>
    if audit.entry.status.isClosed then count + 1 else count
  Json.mkObj [
    ("schemaVersion", toJson (1 : Nat)),
    ("project", toJson "Frontier"),
    ("summary", Json.mkObj [
      ("total", toJson audits.size),
      ("valid", toJson validCount),
      ("closed", toJson closedCount),
      ("globalErrors", toJson globalErrors)
    ]),
    ("entries", Json.arr (audits.map entryJson))
  ]

def containsCI (text query : String) : Bool :=
  text.toLower.contains query.toLower

def findEntry? (id : String) : Option Entry :=
  catalog.find? (·.id == id)

def printEntry (audit : Audit) : IO Unit := do
  IO.println s!"{audit.entry.title} [{audit.entry.status.toString}]"
  IO.println s!"id:           {audit.entry.id}"
  IO.println s!"topic:        {audit.entry.topic}"
  IO.println s!"statement:    {audit.entry.statement}"
  IO.println s!"type:         {audit.statementType}"
  if let some certificate := audit.entry.certificate? then
    IO.println s!"certificate:  {certificate}"
  if let some evidence := audit.entry.evidence? then
    IO.println s!"evidence:     {evidence.toString}"
  IO.println s!"tags:         {", ".intercalate audit.entry.tags.toList}"
  let dependencies := if audit.dependencies.isEmpty then
    "none"
  else
    ", ".intercalate audit.dependencies.toList
  let axioms := if audit.axioms.isEmpty then "none" else ", ".intercalate audit.axioms.toList
  IO.println s!"depends on:   {dependencies}"
  IO.println s!"axioms:       {axioms}"
  IO.println s!"summary:      {audit.entry.summary}"
  if !audit.errors.isEmpty then
    for error in audit.errors do
      IO.eprintln s!"error: {error}"

def runValidate (env : Environment) : IO UInt32 := do
  let (audits, globalErrors) ← auditCatalog env
  let mut invalid := globalErrors.size
  for audit in audits do
    if audit.isValid then
      IO.println s!"ok  {audit.entry.id} ({audit.entry.status.toString})"
    else
      invalid := invalid + 1
      IO.eprintln s!"ERR {audit.entry.id}"
      for error in audit.errors do
        IO.eprintln s!"    {error}"
  for error in globalErrors do
    IO.eprintln s!"ERR {error}"
  IO.println s!"\n{audits.size - invalid}/{audits.size} registry entries passed"
  return if invalid == 0 then 0 else 1

def runList (env : Environment) (query? : Option String) : IO UInt32 := do
  let (audits, _) ← auditCatalog env
  for audit in audits do
    let tags := " ".intercalate audit.entry.tags.toList
    let searchable :=
      s!"{audit.entry.id} {audit.entry.title} {audit.entry.topic} {tags}"
    if query?.all (containsCI searchable) then
      IO.println s!"{audit.entry.id}\t{audit.entry.status.toString}\t{audit.entry.title}"
  return 0

def runShow (env : Environment) (id : String) : IO UInt32 := do
  let some entry := findEntry? id | do
    IO.eprintln s!"unknown registry id '{id}'"
    return 1
  printEntry (← auditEntry env entry)
  return 0

def runSearch (env : Environment) (query : String) (limit : Nat := 25) : IO UInt32 := do
  let mut results : Array (Name × ConstantInfo) := #[]
  for (name, info) in env.constants.toList do
    if results.size < limit then
      match info with
      | .thmInfo _ | .axiomInfo _ =>
          if containsCI name.toString query then
            results := results.push (name, info)
      | _ => pure ()
  if results.isEmpty then
    IO.println s!"No imported theorem names matched '{query}'."
  else
    for (name, info) in results do
      IO.println s!"{name} : {← prettyType env info}"
  return 0

def genericConstants : NameSet :=
  [``Eq, ``Ne, ``Not, ``And, ``Or, ``Exists, ``True, ``False, ``Iff,
    ``OfNat.ofNat, ``HPow.hPow, ``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul]
    |>.foldl (init := {}) NameSet.insert

def suggestionScore (target : NameSet) (info : ConstantInfo) : Nat :=
  let candidate := info.type.getUsedConstantsAsSet
  target.toArray.foldl (init := 0) fun score name =>
    if !genericConstants.contains name && candidate.contains name then score + 1 else score

def runSuggest (env : Environment) (id : String) (limit : Nat := 15) : IO UInt32 := do
  let some entry := findEntry? id | do
    IO.eprintln s!"unknown registry id '{id}'"
    return 1
  let some statementInfo := env.find? entry.statement | do
    IO.eprintln s!"statement declaration '{entry.statement}' does not exist"
    return 1
  let target := statementInfo.type.getUsedConstantsAsSet
  let mut suggestions : Array (Nat × Name × ConstantInfo) := #[]
  for (name, info) in env.constants.toList do
    match info with
    | .thmInfo _ =>
        let score := suggestionScore target info
        let printable := !name.toString.startsWith "_private" && name != entry.statement
        if score > 0 && printable then
          suggestions := suggestions.push (score, name, info)
    | _ => pure ()
  suggestions := suggestions.qsort fun left right =>
    left.1 > right.1 || (left.1 == right.1 && Name.lt left.2.1 right.2.1)
  IO.println s!"Reusable theorem candidates for {entry.title}:"
  for (score, name, info) in suggestions.take limit do
    IO.println s!"[{score}] {name} : {← prettyType env info}"
  if suggestions.isEmpty then
    IO.println "No candidates shared non-generic statement constants."
  return 0

def runGraph (env : Environment) : IO UInt32 := do
  let (audits, _) ← auditCatalog env
  IO.println "flowchart LR"
  for audit in audits do
    IO.println s!"  {audit.entry.id.replace "-" "_"}[\"{audit.entry.title}\"]"
  for audit in audits do
    for dependency in audit.dependencies do
      IO.println s!"  {dependency.replace "-" "_"} --> {audit.entry.id.replace "-" "_"}"
  return 0

def runExport (env : Environment) (path : System.FilePath) : IO UInt32 := do
  let (audits, globalErrors) ← auditCatalog env
  let json := catalogJson audits globalErrors
  if let some parent := path.parent then
    IO.FS.createDirAll parent
  IO.FS.writeFile path (json.pretty 120)
  IO.println s!"Exported {audits.size} entries to {path}"
  return if globalErrors.isEmpty && audits.all Audit.isValid then 0 else 1

def printHelp : IO Unit :=
  IO.println "Frontier: a Lean-checked mathematical research registry\n\n\
    Usage:\n\
      lake exe frontier validate\n\
      lake exe frontier list [query]\n\
      lake exe frontier show <id>\n\
      lake exe frontier search <Lean declaration name>\n\
      lake exe frontier suggest <registry id>\n\
      lake exe frontier graph\n\
      lake exe frontier export [path]\n\n\
    The default export path is build/frontier.json."

def loadEnvironment : IO Environment := do
  initSearchPath (← findSysroot)
  importModules #[{ module := `Leanproofs }] {}

def run (args : List String) : IO UInt32 := do
  match args with
  | ["help"] | ["--help"] | ["-h"] | [] => printHelp *> pure 0
  | command :: rest =>
      let env ← loadEnvironment
      match command, rest with
      | "validate", [] => runValidate env
      | "list", [] => runList env none
      | "list", query => runList env (some (" ".intercalate query))
      | "show", [id] => runShow env id
      | "search", [] => IO.eprintln "search requires a query" *> pure 1
      | "search", query => runSearch env (" ".intercalate query)
      | "suggest", [id] => runSuggest env id
      | "graph", [] => runGraph env
      | "export", [] => runExport env "build/frontier.json"
      | "export", [path] => runExport env path
      | _, _ => IO.eprintln s!"invalid command or arguments: {command}" *> printHelp *> pure 1

end Frontier.CLI

def main (args : List String) : IO UInt32 :=
  Frontier.CLI.run args
