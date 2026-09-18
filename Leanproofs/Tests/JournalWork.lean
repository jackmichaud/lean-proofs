/-
Copyright (c) 2026 Jack Michaud. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Michaud
-/

import Leanproofs.Tests.Support

/-!
# Journal and work tests
-/

open Lean Frontier Frontier.CLI

namespace Frontier.Test

/-! ## Work journal

The journal is untrusted data, but it is *durable* untrusted data: it is what an agent reads to
pick work back up, so a decoder that quietly accepts a wrong file is as bad here as anywhere. -/

/-- Run `action` against an empty journal, and leave it empty afterwards. Tests share one root,
so an item left behind would make a later assertion about counts depend on ordering. -/
def withEmptyJournal {α : Type} (context : Context) (action : IO α) : IO α := do
  let clear : IO Unit := do
    let (items, _) ← Journal.readAll context.workRoot
    for item in items do
      Journal.remove context.workRoot item.id
    -- Files that failed to decode are not returned by `readAll`, so clear the directory too.
    if ← context.workRoot.pathExists then
      for entry in ← context.workRoot.readDir do
        if entry.fileName.endsWith ".json" then
          IO.FS.removeFile entry.path
  clear
  try action finally clear

def testJournalData (suite : Suite) : IO Unit := do
  check suite "slugify lowercases and hyphenates"
    (Journal.slugify "Twin Prime Conjecture" == "twin-prime-conjecture")
  check suite "slugify collapses runs of separators"
    (Journal.slugify "a  --  b" == "a-b")
  check suite "slugify strips trailing separators"
    (Journal.slugify "Catalan's conjecture!" == "catalan-s-conjecture")
  check suite "slugify never returns an empty id" (Journal.slugify "!!!" == "item")
  -- An id becomes a filename, so traversal has to be impossible by construction.
  check suite "a traversal attempt is not a valid id"
    (!Journal.isValidId "../../etc/passwd")
  check suite "an absolute path is not a valid id" (!Journal.isValidId "/tmp/x")
  check suite "an uppercase id is not valid" (!Journal.isValidId "Item")
  check suite "an empty id is not valid" (!Journal.isValidId "")
  check suite "a slug is a valid id" (Journal.isValidId "twin-prime-conjecture")

  let item : Journal.Item := {
    id := "roundtrip"
    title := "Roundtrip"
    goal := "∀ n : ℕ, n = n"
    draft? := some "drafts/x.lean"
    note? := some "a note"
    stage := .blocked
    attempts := 3
    lastCheck? := some {
      checkedAt := "2026-01-01T00:00:00Z"
      path := "drafts/x.lean"
      clean := false
      declarations := 2
      reuses := #["fermat-zmod"]
      axioms := #["propext"]
      errors := #["boom"]
      diagnostics := #["x.lean:1:1: error"]
    }
    created := "2026-01-01T00:00:00Z"
    updated := "2026-01-02T00:00:00Z"
  }
  match Journal.itemOfJson (Journal.itemJson item) with
  | .error message => check suite "an item survives a JSON roundtrip" false message
  | .ok decoded =>
      check suite "an item survives a JSON roundtrip" true
      check suite "a roundtrip preserves the stage" (decoded.stage == .blocked)
      check suite "a roundtrip preserves the attempt count" (decoded.attempts == 3)
      check suite "a roundtrip preserves the goal" (decoded.goal == item.goal)
      check suite "a roundtrip preserves the last check"
        (decoded.lastCheck?.map (·.reuses) == some #["fermat-zmod"])
      check suite "a roundtrip preserves the optional draft path"
        (decoded.draft? == some "drafts/x.lean")

  let decode (text : String) : Except String Journal.Item :=
    match Json.parse text with
    | .error message => .error message
    | .ok json => Journal.itemOfJson json
  check suite "an item with no id is rejected"
    (decode "{\"title\":\"t\",\"stage\":\"exploring\",\"created\":\"x\",\"updated\":\"x\"}"
      |>.toOption.isNone)
  check suite "an item with an unknown stage is rejected"
    (decode "{\"id\":\"a\",\"title\":\"t\",\"stage\":\"finished\",\"created\":\"x\",\
      \"updated\":\"x\"}" |>.toOption.isNone)
  check suite "an item with a traversal id is rejected"
    (decode "{\"id\":\"../x\",\"title\":\"t\",\"stage\":\"exploring\",\"created\":\"x\",\
      \"updated\":\"x\"}" |>.toOption.isNone)
  check suite "an item with a non-string title is rejected"
    (decode "{\"id\":\"a\",\"title\":5,\"stage\":\"exploring\",\"created\":\"x\",\
      \"updated\":\"x\"}" |>.toOption.isNone)

  -- A previously clean item whose draft has broken must not keep advertising `clean`.
  check suite "a failing check demotes a clean item"
    (stageAfterCheck .clean false == .drafting)
  check suite "a passing check marks an item clean"
    (stageAfterCheck .drafting true == .clean)
  check suite "a check does not disturb a registered item"
    (stageAfterCheck .registered false == .registered)
  check suite "a check does not revive an abandoned item"
    (stageAfterCheck .abandoned true == .abandoned)

def testJournalStorage (suite : Suite) (context : Context) : IO Unit :=
  withEmptyJournal context do
    let root := context.workRoot
    let now ← Journal.timestampNow
    check suite "a timestamp is ISO-8601 UTC"
      (now.length == 20 && now.endsWith "Z" && isIsoDate (now.take 10).toString)
      s!"got '{now}'"

    let item : Journal.Item := {
      id := "stored", title := "Stored", created := now, updated := now }
    Journal.write root item
    check suite "a written item exists" (← Journal.exists? root "stored")
    match ← Journal.read? root "stored" with
    | .error message => check suite "a written item reads back" false message
    | .ok loaded =>
        check suite "a written item reads back" true
        check suite "a written item keeps its title" (loaded.title == "Stored")

    check suite "a missing item is reported, not fatal"
      (← Journal.read? root "absent").toOption.isNone

    -- Ids collide as soon as two items share a title, and silently overwriting the first would
    -- lose work.
    check suite "a fresh id is the slug when free" ((← Journal.freshId root "Brand New") == "brand-new")
    check suite "a fresh id is suffixed on collision" ((← Journal.freshId root "Stored") == "stored-2")

    -- One malformed file must not hide the rest of the board, and must not vanish from it.
    IO.FS.writeFile (root / "broken.json") "{ not json"
    let (items, problems) ← Journal.readAll root
    check suite "a malformed file does not hide readable items" (items.size == 1)
      s!"got {items.map (·.id)}"
    check suite "a malformed file is reported" (problems.size == 1) s!"got {problems}"
    check suite "a malformed file names itself"
      (problems.any (containsSubstring · "broken.json")) s!"got {problems}"
    IO.FS.removeFile (root / "broken.json")

    -- A file whose name is not a slug is ignored with a complaint rather than read.
    IO.FS.writeFile (root / "Not A Slug.json") "{}"
    let (_, nameProblems) ← Journal.readAll root
    check suite "a file with a non-slug name is reported"
      (nameProblems.any (containsSubstring · "not a valid item id")) s!"got {nameProblems}"
    IO.FS.removeFile (root / "Not A Slug.json")

    let publishPath : System.FilePath := "build" / "test-work.json"
    let published ← Journal.publish root publishPath
    check suite "publishing writes every item" (published == 1)
    let contents ← IO.FS.readFile publishPath
    match Json.parse contents with
    | .error message => check suite "the published journal is valid JSON" false message
    | .ok json =>
        check suite "the published journal is valid JSON" true
        -- The page and any other consumer should have to see this without reading the docs.
        check suite "the published journal declares itself untrusted"
          ((json.getObjValAs? Bool "trusted").toOption == some false)
        check suite "the published journal carries a schema version"
          ((json.getObjValAs? Nat "schemaVersion").toOption == some 1)
    IO.FS.removeFile publishPath

/-! ## Work commands

Driven through `compute`, the same entry point `serve` and the CLI use, so the assertions cover
argument handling and the evidence rules rather than the helpers underneath them. -/

def testWorkCommands (suite : Suite) (context : Context) : IO Unit :=
  withEmptyJournal context do
    let itemOf : Payload → Option Journal.Item
      | .workItem item _ => some item
      | .draft _ _ _ recorded? => recorded?
      | _ => none
    let failed : Payload → Bool
      | .failure _ => true
      | _ => false
    let message : Payload → String
      | .failure text => text
      | _ => ""

    check suite "an empty journal lists nothing"
      (match ← compute context ["work", "list"] with
        | .work items problems => items.isEmpty && problems.isEmpty
        | _ => false)

    let added ← compute context ["work", "add", "Twin", "prime", "conjecture",
      "--goal", "infinitely many twin primes"]
    let some item := itemOf added
      | check suite "work add returns the item" false s!"got exit {added.exitCode}"
    check suite "work add slugifies the title" (item.id == "twin-prime-conjecture")
      s!"got '{item.id}'"
    check suite "work add keeps the whole title" (item.title == "Twin prime conjecture")
    check suite "work add records the goal" (item.goal == "infinitely many twin primes")
    -- With no draft there is nothing to iterate on, and `drafting` would overstate it.
    check suite "a new item with no draft starts exploring" (item.stage == .exploring)
    check suite "work add starts at zero attempts" (item.attempts == 0)

    check suite "work add requires a title"
      (failed (← compute context ["work", "add"]))

    check suite "work show finds the item"
      (match ← compute context ["work", "show", "twin-prime-conjecture"] with
        | .workItem found _ => found.id == "twin-prime-conjecture"
        | _ => false)
    check suite "work show reports an unknown id"
      (failed (← compute context ["work", "show", "no-such-item"]))
    -- The id reaches the filesystem, so the shape is rejected before it gets there.
    let traversal ← compute context ["work", "show", "../../etc/passwd"]
    check suite "work show rejects a traversal id" (failed traversal)
    check suite "work show says why a traversal id is invalid"
      (containsSubstring (message traversal) "not a valid work item id")
      s!"got '{message traversal}'"

    -- The evidence rules. These are the point of the stage field: a board whose stages could
    -- be typed in would report progress nothing had verified.
    let handClean ← compute context
      ["work", "set", "twin-prime-conjecture", "--stage", "clean"]
    check suite "`clean` cannot be set by hand" (failed handClean)
    check suite "`clean` explains that a check sets it"
      (containsSubstring (message handClean) "frontier check --work")
      s!"got '{message handClean}'"

    let handRegistered ← compute context
      ["work", "set", "twin-prime-conjecture", "--stage", "registered"]
    check suite "`registered` cannot be set without an entry" (failed handRegistered)

    check suite "`registered` cannot name a catalog entry that does not exist"
      (failed (← compute context
        ["work", "set", "twin-prime-conjecture", "--stage", "registered",
         "--entry", "no-such-entry"]))

    let registered ← compute context
      ["work", "set", "twin-prime-conjecture", "--stage", "registered",
       "--entry", "fermat-zmod"]
    check suite "`registered` is accepted with a real catalog entry"
      (itemOf registered |>.any fun found => found.stage == .registered)
      s!"got exit {registered.exitCode}"
    check suite "`registered` records which entry"
      (itemOf registered |>.any fun found => found.entry? == some "fermat-zmod")

    -- Ordinary stages are plain metadata and set freely.
    check suite "an ordinary stage is set freely"
      (itemOf (← compute context
        ["work", "set", "twin-prime-conjecture", "--stage", "blocked",
         "--note", "needs a bound"]) |>.any fun found =>
          found.stage == .blocked && found.note? == some "needs a bound")

    check suite "work set needs something to set"
      (failed (← compute context ["work", "set", "twin-prime-conjecture"]))
    check suite "work set rejects an unknown stage"
      (failed (← compute context
        ["work", "set", "twin-prime-conjecture", "--stage", "finished"]))
    -- A draft path that does not resolve would sit in the journal until someone wondered why
    -- `check --work` kept reporting a missing file.
    check suite "work set rejects a draft that does not exist"
      (failed (← compute context
        ["work", "set", "twin-prime-conjecture", "--draft", "no/such/draft.lean"]))
    check suite "work list rejects an unknown stage"
      (failed (← compute context ["work", "list", "--stage", "finished"]))
    check suite "work list filters by stage"
      (match ← compute context ["work", "list", "--stage", "blocked"] with
        | .work items _ => items.size == 1
        | _ => false)
    check suite "work list excludes other stages"
      (match ← compute context ["work", "list", "--stage", "exploring"] with
        | .work items _ => items.isEmpty
        | _ => false)
    check suite "an unknown work subcommand is reported"
      (failed (← compute context ["work", "frobnicate"]))

    check suite "work remove deletes the item"
      (match ← compute context ["work", "remove", "twin-prime-conjecture"] with
        | .workRemoved id => id == "twin-prime-conjecture"
        | _ => false)
    check suite "a removed item is gone"
      (!(← Journal.exists? context.workRoot "twin-prime-conjecture"))
    check suite "work remove reports an unknown id"
      (failed (← compute context ["work", "remove", "twin-prime-conjecture"]))

def testCheckRecording (suite : Suite) (context : Context) : IO Unit :=
  withEmptyJournal context do
    let itemOf : Payload → Option Journal.Item
      | .workItem item _ => some item
      | .draft _ _ _ recorded? => recorded?
      | _ => none

    let added ← compute context ["work", "add", "Recording"]
    let some item := itemOf added | check suite "the recording fixture is created" false
    check suite "the recording fixture starts exploring" (item.stage == .exploring)

    -- A clean draft: the report has to land on the item, not just on stdout.
    withDraft
      "theorem draft_recorded (p : ℕ) [Fact p.Prime] (a : ZMod p) : a ^ p = a :=\n  \
       FermatFromScratch.pow_card p a\n"
      fun path => do
        let payload ← compute context ["check", "--work", "recording", path.toString]
        let some recorded := itemOf payload
          | check suite "a check records against the item" false s!"got exit {payload.exitCode}"
        check suite "a passing check marks the item clean" (recorded.stage == .clean)
        check suite "a check increments the attempt count" (recorded.attempts == 1)
        check suite "a check records the draft path" (recorded.draft? == some path.toString)
        -- The reason the journal is worth keeping: the reuse and axioms, not just a verdict.
        check suite "a check records catalog reuse"
          (recorded.lastCheck?.any (·.reuses.contains "fermat-zmod"))
          s!"got {recorded.lastCheck?.map (·.reuses)}"
        check suite "a check records the axioms"
          (recorded.lastCheck?.any (·.axioms.contains "propext"))
        check suite "a clean check is recorded as clean"
          (recorded.lastCheck?.any (·.clean))
        check suite "the record survives a reload"
          (match ← Journal.read? context.workRoot "recording" with
            | .ok reloaded => reloaded.stage == .clean && reloaded.attempts == 1
            | .error _ => false)

    -- Now break it. The item was `clean`; it must not stay that way.
    withDraft "theorem draft_recorded_broken : (1 : Nat) = 2 := by sorry\n" fun path => do
      let payload ← compute context ["check", "--work", "recording", path.toString]
      let some recorded := itemOf payload
        | check suite "a failing check records against the item" false
      check suite "a failing check demotes a clean item" (recorded.stage == .drafting)
        s!"got {recorded.stage.toString}"
      check suite "a failing check still increments attempts" (recorded.attempts == 2)
      check suite "a failing check records the policy violation"
        (recorded.lastCheck?.any fun record =>
          record.errors.any (containsSubstring · "sorryAx"))
        s!"got {recorded.lastCheck?.map (·.errors)}"
      check suite "a failing check records Lean's diagnostics"
        (recorded.lastCheck?.any (!·.diagnostics.isEmpty))

    -- A report that never elaborated is not an attempt. Recording one bumps the counter,
    -- overwrites `draft?` with a path that may not exist, and demotes a `clean` item — all on
    -- a caller error rather than anything about the draft. The item is at attempt 2 and
    -- `drafting` from the checks above, and must still be after each of these.
    let untouched (name : String) : IO Unit := do
      match ← Journal.read? context.workRoot "recording" with
      | .error message => check suite name false message
      | .ok reloaded =>
          check suite name (reloaded.attempts == 2 && reloaded.draft? != some "no-such-file.lean")
            s!"attempts {reloaded.attempts}, draft {reloaded.draft?}"

    let missing ← compute context ["check", "--work", "recording", "no-such-file.lean"]
    check suite "a check on a missing file still fails" (missing.exitCode != 0)
    check suite "a missing draft file is not recorded as an attempt"
      (match missing with
        | .draft _ _ requested? recorded? => requested? == some "recording" && recorded?.isNone
        | _ => false)
    untouched "a missing draft file leaves the item untouched"

    withDraft "import Not.A.Real.Module\n\ntheorem draft_bad_import : True := trivial\n"
      fun path => do
        let payload ← compute context ["check", "--work", "recording", path.toString]
        check suite "an unavailable import is not recorded as an attempt"
          (match payload with
            | .draft _ _ requested? recorded? => requested? == some "recording" && recorded?.isNone
            | _ => false)
        untouched "an unavailable import leaves the item untouched"

    check suite "check reports an unknown work id"
      (match ← compute context ["check", "--work", "no-such-item", "whatever.lean"] with
        | .failure _ => true
        | _ => false)
    -- Reporting the missing item rather than the missing file, and without having elaborated
    -- anything: the item is looked up before the draft is read.
    check suite "an unknown work id is not recorded as an attempt"
      (!(← Journal.exists? context.workRoot "no-such-item"))

end Frontier.Test

