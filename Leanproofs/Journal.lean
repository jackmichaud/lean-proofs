/-
Copyright (c) 2026 Jack Michaud. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Michaud
-/

import Leanproofs.Research.Events

/-!
# Work journal projection

The append-only streams in `Frontier.Research` are the authoritative work store. This module
keeps the compact work-item shape used by the CLI and static web export, but every value is
materialized from a validated event stream. Research history is never rewritten or deleted.
-/

open Lean

namespace Frontier.Journal

abbrev Stage := Research.Stage

def stages : Array Stage :=
  #[.exploring, .drafting, .blocked, .clean, .registered, .abandoned]

def stageNames : Array String := stages.map Research.Stage.toString

def Stage.ofString? (value : String) : Option Stage :=
  (Research.Stage.ofString value).toOption

def Stage.handSetError? : Stage → Option String
  | .clean => some
      "`clean` records that Lean accepted a draft, so it is set by `frontier check --work <id>` and not by hand"
  | .registered => some
      "`registered` records a promotion event, so it requires `--entry <catalog id>` naming a clean result"
  | _ => none

def timestampNow : IO String := Research.timestampNow

structure CheckRecord where
  checkedAt : String
  path : String
  clean : Bool
  declarations : Nat
  reuses : Array String := #[]
  axioms : Array String := #[]
  errors : Array String := #[]
  diagnostics : Array String := #[]
  deriving Inhabited, Repr

/-- Derived presentation record. It is never serialized as authoritative state. -/
structure Item where
  id : String
  title : String
  goal : String := ""
  draft? : Option String := none
  note? : Option String := none
  entry? : Option String := none
  stage : Stage := .exploring
  attempts : Nat := 0
  lastCheck? : Option CheckRecord := none
  created : String
  updated : String
  deriving Inhabited, Repr

def slugify (value : String) : String :=
  let mapped := value.toLower.toList.map fun c =>
    if c.isAlphanum && c.toNat < 128 then c else '-'
  let collapsed := mapped.foldl (init := "") fun accumulated c =>
    if c == '-' && (accumulated.isEmpty || accumulated.back == '-') then accumulated
    else accumulated.push c
  let trimmed := (collapsed.toList.reverse.dropWhile (· == '-')).reverse |> String.ofList
  if trimmed.isEmpty then "item" else trimmed

def isValidId (id : String) : Bool :=
  !id.isEmpty && id == slugify id

def optionJson : Option String → Json
  | some value => toJson value
  | none => Json.null

def checkRecordJson (record : CheckRecord) : Json :=
  Json.mkObj [
    ("checkedAt", toJson record.checkedAt),
    ("path", toJson record.path),
    ("clean", toJson record.clean),
    ("declarations", toJson record.declarations),
    ("reuses", toJson record.reuses),
    ("axioms", toJson record.axioms),
    ("errors", toJson record.errors),
    ("diagnostics", toJson record.diagnostics)
  ]

def itemJson (item : Item) : Json :=
  Json.mkObj [
    ("id", toJson item.id),
    ("title", toJson item.title),
    ("goal", toJson item.goal),
    ("draft", optionJson item.draft?),
    ("note", optionJson item.note?),
    ("entry", optionJson item.entry?),
    ("stage", toJson item.stage.toString),
    ("attempts", toJson item.attempts),
    ("lastCheck", match item.lastCheck? with
      | some record => checkRecordJson record
      | none => Json.null),
    ("created", toJson item.created),
    ("updated", toJson item.updated)
  ]

def defaultRoot : IO System.FilePath := do
  match ← IO.getEnv "FRONTIER_WORK_DIR" with
  | some value => if value.trimAscii.isEmpty then return "work" else return value
  | none => return "work"

def defaultExportPath : System.FilePath := "web" / "data" / "work.json"

private def attemptId (id : String) : Except String Research.AttemptId := do
  unless isValidId id do
    throw s!"'{id}' is not a valid work item id; ids are lowercase alphanumerics and hyphens"
  Research.AttemptId.parse id

def streamPath (root : System.FilePath) (id : String) : Except String System.FilePath := do
  Research.streamPath root (← attemptId id)

def exists? (root : System.FilePath) (id : String) : IO Bool := do
  let path ← match streamPath root id with
    | .ok path => pure path
    | .error _ => return false
  path.pathExists

private def checkRecord (summary : Research.AttemptSummary) : Option CheckRecord := do
  let checked ← summary.lastCheck?
  let checkedAt ← summary.lastCheckAt?
  return {
    checkedAt
    path := checked.artifact
    clean := checked.clean
    declarations := checked.declarations
    reuses := checked.reuses
    axioms := checked.axioms
    errors := checked.errors
    diagnostics := checked.diagnostics
  }

def itemOfSummary (summary : Research.AttemptSummary) : Item := {
  id := summary.attemptId.value
  title := summary.title
  goal := summary.goal
  draft? := summary.draftPath?
  note? := summary.note?
  entry? := summary.promotedCatalogId?
  stage := summary.stage
  attempts := summary.artifactChecks
  lastCheck? := checkRecord summary
  created := summary.createdAt
  updated := summary.updatedAt
}

def read? (root : System.FilePath) (id : String) : IO (Except String Item) := do
  let attempt ← match attemptId id with
    | .ok value => pure value
    | .error message => return .error message
  let path ← match Research.streamPath root attempt with
    | .ok value => pure value
    | .error message => return .error message
  unless ← path.pathExists do
    return .error s!"no work item '{id}'"
  match ← Research.readSummary root attempt with
  | .ok summary => return .ok (itemOfSummary summary)
  | .error message => return .error message

/-- Materialize every valid stream. Problems are returned for presentation instead of hiding
the healthy streams. -/
def readAll (root : System.FilePath) : IO (Array Item × Array String) := do
  unless ← root.pathExists do return (#[], #[])
  let mut items := #[]
  let mut problems := #[]
  for entry in ← root.readDir do
    let name := entry.fileName
    unless name.endsWith ".jsonl" do continue
    let id := String.ofList (name.toList.take (name.length - 6))
    match ← read? root id with
    | .ok item => items := items.push item
    | .error message => problems := problems.push s!"{entry.path}: {message}"
  let sorted := items.qsort fun left right =>
    if left.updated != right.updated then left.updated > right.updated else left.id < right.id
  return (sorted, problems.qsort (· < ·))

def freshId (root : System.FilePath) (title : String) : IO String := do
  let base := slugify title
  unless ← exists? root base do return base
  let mut suffix := 2
  while ← exists? root s!"{base}-{suffix}" do suffix := suffix + 1
  return s!"{base}-{suffix}"

/-- Append a nonempty batch as one process-safe transaction and return its materialized work item. -/
def appendMany (root : System.FilePath) (id : String)
    (environment : Research.EnvironmentFingerprint) (actor : Research.Actor)
    (payloads : Array Research.Payload) : IO (Except String Item) := do
  if payloads.isEmpty then return .error "cannot append an empty research event batch"
  let attempt ← match attemptId id with
    | .ok value => pure value
    | .error message => return .error message
  let events ← match ← Research.appendPayloads root attempt environment actor payloads with
    | .ok values => pure values
    | .error message => return .error message
  let summary ← match Research.materialize attempt events with
    | .ok value => pure value
    | .error message => return .error message
  return .ok (itemOfSummary summary)

/-- Append one validated event and return the newly materialized work item. -/
def append (root : System.FilePath) (id : String)
    (environment : Research.EnvironmentFingerprint) (actor : Research.Actor)
    (payload : Research.Payload) : IO (Except String Item) :=
  appendMany root id environment actor #[payload]

def journalJson (items : Array Item) (problems : Array String) (generated : String) : Json :=
  let count (predicate : Item → Bool) : Nat :=
    items.foldl (init := 0) fun total item => if predicate item then total + 1 else total
  Json.mkObj [
    ("schemaVersion", toJson (2 : Nat)),
    ("generated", toJson generated),
    ("trusted", toJson false),
    ("note", toJson Research.trustNotice),
    ("stages", toJson stageNames),
    ("counts", Json.mkObj (stages.toList.map fun stage =>
      (stage.toString, toJson (count (·.stage == stage))))),
    ("problems", toJson problems),
    ("items", Json.arr (items.map itemJson))
  ]

def publish (root : System.FilePath) (path : System.FilePath) : IO Nat := do
  let lock : System.FilePath := path.toString ++ ".lock"
  let temporary : System.FilePath := path.toString ++ ".tmp"
  Research.withFileLock lock true do
    let (items, problems) ← readAll root
    let contents := (journalJson items problems (← timestampNow)).pretty 100 ++ "\n"
    try
      if ← temporary.pathExists then IO.FS.removeFile temporary
      do
        let handle ← IO.FS.Handle.mk temporary .write
        handle.putStr contents
        handle.flush
      IO.FS.rename temporary path
    catch exception =>
      if ← temporary.pathExists then IO.FS.removeFile temporary
      throw exception
    return items.size

end Frontier.Journal
