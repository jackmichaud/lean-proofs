/-
Copyright (c) 2026 Jack Michaud. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Michaud
-/

import Lean
import Std.Time

/-!
# The work journal

A durable, *untrusted* record of research in progress. `frontier check` is stateless: it tells
you whether a file is acceptable and then forgets. Everything between "here is a goal" and
"here is a catalog entry" — what was attempted, what Lean said, which draft is closest, what is
blocked and why — had nowhere to live, so it did not survive the session that produced it.

The journal is that place. One JSON file per item under `work/`, so concurrent writers do not
contend and a diff shows what changed.

## What this is not

This is a **local work journal**, not a submission endpoint. The distinction is the whole
reason it can exist today: the sandbox requirements in `docs/retrieval-and-agents.md` apply to
accepting Lean from an untrusted party, and nothing here accepts anything from anywhere. An
agent working in this checkout records what it is already doing. Reading a journal file is not
running it, and `work` never elaborates, builds, or executes.

## Trust boundary

The journal is outside the trust base and says so in its own exported data (`trusted: false`).
It is metadata about attempts, not evidence about mathematics. Two stages are nonetheless
*evidence-backed* and cannot be asserted by hand:

* `clean` is written only by `frontier check --work`, from a report that actually passed.
* `registered` requires naming a catalog entry that exists.

That mirrors the registry itself, where `status` must be backed by a certificate. A journal
whose stages could be set by fiat would be a progress bar an agent could fill in by typing.
-/

open Lean

namespace Frontier.Journal

/-! ## Time

UTC, computed from the epoch rather than through a local-zone lookup: the journal is read by
tooling and compared across machines, and a timestamp whose meaning depends on the writer's
`TZ` is not comparable. This also avoids depending on a timezone database being present. -/

def utcNow : IO Std.Time.PlainDateTime := do
  let timestamp ← Std.Time.Timestamp.now
  return Std.Time.PlainDateTime.ofWallTime
    (Std.Time.WallTime.ofTimestamp timestamp Std.Time.TimeZone.Offset.zero)

/-- The current UTC instant as `YYYY-MM-DDTHH:MM:SSZ`. -/
def timestampNow : IO String := do
  return (← utcNow).format "yyyy-MM-dd'T'HH:mm:ss'Z'"

/-! ## Stages -/

/-- Where an item stands. Deliberately not the submission-state table in
`docs/retrieval-and-agents.md`: those states describe a candidate moving through a validator
that accepts untrusted input, and these describe work an author or agent is doing in a
checkout. Conflating them would suggest a sandbox exists. -/
inductive Stage where
  /-- A goal, with no draft yet. -/
  | exploring
  /-- A draft exists and is being iterated on. -/
  | drafting
  /-- Stuck, with the reason recorded in the note. -/
  | blocked
  /-- `frontier check` accepted the draft: Lean elaborated it and the axiom policy passed. -/
  | clean
  /-- Promoted into the catalog. -/
  | registered
  /-- Dropped. Kept, because knowing an approach failed is worth more than a tidy board. -/
  | abandoned
  deriving BEq, DecidableEq, Inhabited, Repr

def Stage.toString : Stage → String
  | .exploring => "exploring"
  | .drafting => "drafting"
  | .blocked => "blocked"
  | .clean => "clean"
  | .registered => "registered"
  | .abandoned => "abandoned"

def Stage.ofString? : String → Option Stage
  | "exploring" => some .exploring
  | "drafting" => some .drafting
  | "blocked" => some .blocked
  | "clean" => some .clean
  | "registered" => some .registered
  | "abandoned" => some .abandoned
  | _ => none

/-- Every stage, in board order. -/
def stages : Array Stage :=
  #[.exploring, .drafting, .blocked, .clean, .registered, .abandoned]

def stageNames : Array String := stages.map Stage.toString

/-- Why `stage` cannot be set directly, if it cannot. -/
def Stage.handSetError? : Stage → Option String
  | .clean => some
      "`clean` records that Lean accepted a draft, so it is set by `frontier check --work <id>` \
       and not by hand"
  | .registered => some
      "`registered` records that a catalog entry exists, so it requires `--entry <catalog id>` \
       naming one"
  | _ => none

/-! ## Records -/

/-- The outcome of one `frontier check` against an item's draft.

This is the payload that makes the journal worth keeping: not "attempt failed" but the axioms,
the catalog reuse, and Lean's own diagnostics, which is what a later session needs in order to
pick the work back up. -/
structure CheckRecord where
  checkedAt : String
  path : String
  clean : Bool
  declarations : Nat
  /-- Catalog ids the draft's proofs reach. -/
  reuses : Array String := #[]
  axioms : Array String := #[]
  /-- Axiom-policy violations and fatal failures. -/
  errors : Array String := #[]
  /-- Lean's diagnostics, already prefixed with `file:line:col`. -/
  diagnostics : Array String := #[]
  deriving Inhabited, Repr

structure Item where
  id : String
  title : String
  /-- The goal, informal or as a Lean proposition. Free text on purpose: an item exists before
  the statement is formal, which is the point of having one. -/
  goal : String := ""
  /-- Path to the draft `.lean` file, once there is one. -/
  draft? : Option String := none
  note? : Option String := none
  /-- The catalog entry this became, once `registered`. -/
  entry? : Option String := none
  stage : Stage := .exploring
  /-- How many times `frontier check --work` has run against this item. -/
  attempts : Nat := 0
  lastCheck? : Option CheckRecord := none
  created : String
  updated : String
  deriving Inhabited, Repr

/-! ## Identifiers -/

/-- A filesystem- and URL-safe slug. Also the guard against path traversal: an id becomes a
filename, so anything that is not `[a-z0-9-]` has to go before it gets there. -/
def slugify (value : String) : String :=
  let mapped := value.toLower.toList.map fun c =>
    if c.isAlphanum && c.toNat < 128 then c else '-'
  let collapsed := mapped.foldl (init := "") fun accumulated c =>
    if c == '-' && (accumulated.isEmpty || accumulated.back == '-') then accumulated
    else accumulated.push c
  let trimmed := (collapsed.toList.reverse.dropWhile (· == '-')).reverse |> String.ofList
  if trimmed.isEmpty then "item" else trimmed

/-- Whether `id` is a slug this module would have produced. Checked on *read* as well as write:
a file dropped into `work/` by hand must not be able to name itself `../../etc/anything`. -/
def isValidId (id : String) : Bool :=
  !id.isEmpty && id == slugify id

/-! ## JSON -/

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

def optionJson : Option String → Json
  | some value => toJson value
  | none => Json.null

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

/-! ### Decoding

Hand-written rather than `deriving FromJson`, because a journal file is edited by hand and by
other tools. The failure that matters is a file that decodes to something plausible but wrong,
so every field says what it wanted and the caller reports which file was at fault. -/

private def stringField (json : Json) (key : String) : Except String String :=
  match json.getObjVal? key with
  | .error _ => .error s!"missing required string field '{key}'"
  | .ok value =>
      match value.getStr? with
      | .ok text => .ok text
      | .error _ => .error s!"field '{key}' must be a string"

private def optionalString (json : Json) (key : String) : Except String (Option String) :=
  match json.getObjVal? key with
  | .error _ => .ok none
  | .ok Json.null => .ok none
  | .ok value =>
      match value.getStr? with
      | .ok text => .ok (if text.isEmpty then none else some text)
      | .error _ => .error s!"field '{key}' must be a string or null"

private def stringArray (json : Json) (key : String) : Except String (Array String) :=
  match json.getObjVal? key with
  | .error _ => .ok #[]
  | .ok Json.null => .ok #[]
  | .ok value =>
      match value.getArr? with
      | .error _ => .error s!"field '{key}' must be an array of strings"
      | .ok values =>
          values.foldlM (init := #[]) fun accumulated element =>
            match element.getStr? with
            | .ok text => .ok (accumulated.push text)
            | .error _ => .error s!"field '{key}' must be an array of strings"

private def natField (json : Json) (key : String) : Except String Nat :=
  match json.getObjVal? key with
  | .error _ => .ok 0
  | .ok Json.null => .ok 0
  | .ok value =>
      match value.getNat? with
      | .ok number => .ok number
      | .error _ => .error s!"field '{key}' must be a non-negative integer"

private def boolField (json : Json) (key : String) : Except String Bool :=
  match json.getObjVal? key with
  | .error _ => .ok false
  | .ok value =>
      match value.getBool? with
      | .ok flag => .ok flag
      | .error _ => .error s!"field '{key}' must be a boolean"

def checkRecordOfJson (json : Json) : Except String CheckRecord := do
  return {
    checkedAt := ← stringField json "checkedAt"
    path := ← stringField json "path"
    clean := ← boolField json "clean"
    declarations := ← natField json "declarations"
    reuses := ← stringArray json "reuses"
    axioms := ← stringArray json "axioms"
    errors := ← stringArray json "errors"
    diagnostics := ← stringArray json "diagnostics"
  }

def itemOfJson (json : Json) : Except String Item := do
  let id ← stringField json "id"
  unless isValidId id do
    throw s!"'{id}' is not a valid item id; ids are lowercase alphanumerics and hyphens"
  let stageText ← stringField json "stage"
  let some stage := Stage.ofString? stageText
    | throw s!"unknown stage '{stageText}'; expected one of \
               {", ".intercalate stageNames.toList}"
  let lastCheck? ←
    match json.getObjVal? "lastCheck" with
    | .error _ => pure none
    | .ok Json.null => pure none
    | .ok value => some <$> checkRecordOfJson value
  return {
    id, stage, lastCheck?
    title := ← stringField json "title"
    goal := (← optionalString json "goal").getD ""
    draft? := ← optionalString json "draft"
    note? := ← optionalString json "note"
    entry? := ← optionalString json "entry"
    attempts := ← natField json "attempts"
    created := ← stringField json "created"
    updated := ← stringField json "updated"
  }

/-! ## Storage

One file per item. A single journal file would make two agents writing concurrently lose each
other's work, and would turn every update into a whole-journal diff. -/

/-- Default journal directory, overridable with `FRONTIER_WORK_DIR`.

The root is threaded explicitly through every function below rather than read from the
environment at each call, so the tests operate on a temporary directory without mutating
process state — and so nothing can accidentally write to the real journal during a test. -/
def defaultRoot : IO System.FilePath := do
  match ← IO.getEnv "FRONTIER_WORK_DIR" with
  | some value => if value.trimAscii.isEmpty then return "work" else return value
  | none => return "work"

def itemPath (root : System.FilePath) (id : String) : System.FilePath :=
  root / s!"{id}.json"

def write (root : System.FilePath) (item : Item) : IO Unit := do
  IO.FS.createDirAll root
  IO.FS.writeFile (itemPath root item.id) ((itemJson item).pretty 100 ++ "\n")

def exists? (root : System.FilePath) (id : String) : IO Bool :=
  (itemPath root id).pathExists

/-- Read one item, naming the file in any failure. A journal is hand-editable, so "some item
somewhere is malformed" is a useless diagnostic. -/
def read? (root : System.FilePath) (id : String) : IO (Except String Item) := do
  let path := itemPath root id
  unless ← path.pathExists do
    return .error s!"no work item '{id}'"
  let contents ← IO.FS.readFile path
  match Json.parse contents with
  | .error message => return .error s!"{path}: invalid JSON: {message}"
  | .ok json =>
      match itemOfJson json with
      | .error message => return .error s!"{path}: {message}"
      | .ok item =>
          if item.id != id then
            return .error s!"{path}: declares id '{item.id}' but is stored as '{id}'"
          return .ok item

/-- Every item, newest first, alongside the files that could not be read.

Malformed files are reported rather than skipped or fatal: one bad file must not hide the rest
of the journal, and must not silently disappear from a board a human is reading. -/
def readAll (root : System.FilePath) : IO (Array Item × Array String) := do
  unless ← root.pathExists do
    return (#[], #[])
  let mut items := #[]
  let mut problems := #[]
  for entry in ← root.readDir do
    let name := entry.fileName
    unless name.endsWith ".json" do
      continue
    let id := String.ofList (name.toList.take (name.length - 5))
    unless isValidId id do
      problems := problems.push
        s!"{entry.path}: '{id}' is not a valid item id; ignoring the file"
      continue
    match ← read? root id with
    | .error message => problems := problems.push message
    | .ok item => items := items.push item
  let sorted := items.qsort fun left right =>
    if left.updated != right.updated then left.updated > right.updated else left.id < right.id
  return (sorted, problems.qsort (· < ·))

def remove (root : System.FilePath) (id : String) : IO Unit := do
  let path := itemPath root id
  if ← path.pathExists then
    IO.FS.removeFile path

/-! ## Aggregate export

The web workspace is a static page and cannot list a directory, so the journal is published as
one file. Every mutation rewrites it, which is what makes the page follow along without anyone
remembering to run an export step — unlike the catalog, where the committed copy is
deliberately gated by CI because it is trusted data. -/

def defaultExportPath : System.FilePath := "web" / "data" / "work.json"

def journalJson (items : Array Item) (problems : Array String) (generated : String) : Json :=
  let count (predicate : Item → Bool) : Nat :=
    items.foldl (init := 0) fun total item => if predicate item then total + 1 else total
  Json.mkObj [
    ("schemaVersion", toJson (1 : Nat)),
    ("generated", toJson generated),
    -- Stated in the data, not only in the docs. Anything consuming this file should have to
    -- notice that it is a record of attempts and not evidence about mathematics.
    ("trusted", toJson false),
    ("note", toJson "Work in progress. Untrusted: a record of attempts, not verified results."),
    ("stages", toJson stageNames),
    ("counts", Json.mkObj (stages.toList.map fun stage =>
      (stage.toString, toJson (count (·.stage == stage))))),
    ("problems", toJson problems),
    ("items", Json.arr (items.map itemJson))
  ]

/-- Publish the journal to `path`. Called after every mutation. -/
def publish (root : System.FilePath) (path : System.FilePath) : IO Nat := do
  let (items, problems) ← readAll root
  if let some parent := path.parent then
    IO.FS.createDirAll parent
  let json := journalJson items problems (← timestampNow)
  IO.FS.writeFile path (json.pretty 100 ++ "\n")
  return items.size

/-- Write `item` and republish, so the page a human is watching is never behind the journal. -/
def save (root : System.FilePath) (publish? : Option System.FilePath) (item : Item) :
    IO Unit := do
  write root item
  if let some path := publish? then
    _ ← publish root path

/-! ## Identifier allocation -/

/-- A free id derived from `title`, suffixed only when it collides. -/
def freshId (root : System.FilePath) (title : String) : IO String := do
  let base := slugify title
  unless ← exists? root base do
    return base
  let mut suffix := 2
  while ← exists? root s!"{base}-{suffix}" do
    suffix := suffix + 1
  return s!"{base}-{suffix}"

end Frontier.Journal
