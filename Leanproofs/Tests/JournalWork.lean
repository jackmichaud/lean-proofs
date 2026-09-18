/-
Copyright (c) 2026 Jack Michaud. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Michaud
-/

import Leanproofs.Tests.Support

/-! Event-backed work journal tests. -/

open Lean Frontier Frontier.CLI

namespace Frontier.Test

def withEmptyJournal {α : Type} (context : Context) (action : IO α) : IO α := do
  let clear : IO Unit := do
    if ← context.workRoot.pathExists then
      for entry in ← context.workRoot.readDir do
        if entry.fileName.endsWith ".jsonl" || entry.fileName.endsWith ".lock" ||
            entry.fileName.endsWith ".tmp" then
          IO.FS.removeFile entry.path
  clear
  try action finally clear

private def itemOf : Payload → Option Journal.Item
  | .workItem item _ => some item
  | .draft _ _ _ recorded? => recorded?
  | _ => none

private def failed : Payload → Bool
  | .failure _ => true
  | _ => false

def testJournalData (suite : Suite) : IO Unit := do
  check suite "slugify lowercases and hyphenates"
    (Journal.slugify "Twin Prime Conjecture" == "twin-prime-conjecture")
  check suite "slugify collapses separators" (Journal.slugify "a -- b" == "a-b")
  check suite "slugify never returns empty" (Journal.slugify "!!!" == "item")
  check suite "traversal is not a valid id" (!Journal.isValidId "../../etc/passwd")
  check suite "a slug is a valid id" (Journal.isValidId "twin-prime-conjecture")
  check suite "failed check demotes clean" (stageAfterCheck .clean false == .drafting)
  check suite "check preserves abandoned" (stageAfterCheck .abandoned true == .abandoned)

def testJournalStorage (suite : Suite) (context : Context) : IO Unit :=
  withEmptyJournal context do
    let now ← Journal.timestampNow
    check suite "timestamp is canonical UTC"
      (now.length == 20 && now.endsWith "Z" && isIsoDate (now.take 10).toString)
    let added ← workAdd context "Stored" (some "goal") none none
    let some item := itemOf added | check suite "work item created" false
    check suite "creation materializes item" (item.id == "stored" && item.goal == "goal")
    let path := (Journal.streamPath context.workRoot "stored").toOption.get!
    check suite "authoritative store is JSONL" (← path.pathExists)
    check suite "mutable item JSON is absent" (!(← (context.workRoot / "stored.json").pathExists))
    match ← Research.readEvents context.workRoot ⟨"stored"⟩ with
    | .error message => check suite "created stream validates" false message
    | .ok events =>
        check suite "created stream validates" (events.size == 1)
        check suite "first event creates attempt"
          (match events[0]!.payload with | .attemptCreated _ => true | _ => false)
        check suite "research events use the session fingerprint"
          (events[0]!.environment == context.fingerprint.environment)
        check suite "policy provenance is content-derived"
          (events[0]!.environment.policyVersion.startsWith "sha256:")
    let publishPath : System.FilePath := "build" / "test-work.json"
    let count ← Journal.publish context.workRoot publishPath
    check suite "publish materializes streams" (count == 1)
    let published ← IO.FS.readFile publishPath
    let trusted? := (Json.parse published).toOption.bind fun json =>
      (json.getObjValAs? Bool "trusted").toOption
    check suite "published view is untrusted" (trusted? == some false)
    let publishTasks ← (Array.range 8).mapM fun _ => IO.asTask (Journal.publish context.workRoot publishPath)
    let mut publishesOk := true
    for task in publishTasks do
      match ← IO.wait task with
      | .ok count => publishesOk := publishesOk && count == 1
      | .error _ => publishesOk := false
    check suite "concurrent journal publication is serialized" publishesOk
    check suite "concurrent publication leaves valid JSON"
      ((Json.parse (← IO.FS.readFile publishPath)).toOption.isSome)
    check suite "publication leaves no temporary file"
      (!(← (publishPath.toString ++ ".tmp" : System.FilePath).pathExists))
    IO.FS.removeFile publishPath
    let publishLock : System.FilePath := publishPath.toString ++ ".lock"
    if ← publishLock.pathExists then IO.FS.removeFile publishLock

    let batched ← appendResearch context item.id {
      kind := .agent
      name := "journal-batch-test"
      runId := ⟨"journal-batch-test"⟩
    } #[
      .metadataUpdated { metadata := {
        title := item.title
        goal := "refined goal"
        note? := some "batched update"
      } },
      .stageChanged {
        fromStage := .exploring
        toStage := .blocked
        reason? := some "waiting for a lemma"
      }
    ]
    match batched with
    | .error message => check suite "multi-event append succeeds" false message
    | .ok updated =>
        check suite "multi-event append succeeds"
          (updated.goal == "refined goal" && updated.stage == .blocked)
    match ← Research.readEvents context.workRoot ⟨item.id⟩ with
    | .error message => check suite "batch events are contiguous" false message
    | .ok events =>
        check suite "batch events are contiguous"
          (events.size == 3 && events[1]!.sequence == 2 && events[2]!.sequence == 3)
        check suite "batch event ids follow their sequences"
          (events[1]!.eventId.value == "event-2" && events[2]!.eventId.value == "event-3")
        check suite "batch events share one timestamp"
          (events[1]!.occurredAt == events[2]!.occurredAt)

    let before ← IO.FS.readFile path
    let rejected ← appendResearch context item.id {
      kind := .agent
      name := "journal-batch-test"
      runId := ⟨"journal-batch-test"⟩
    } #[
      .metadataUpdated { metadata := {
        title := item.title
        goal := "must not be written"
      } },
      .stageChanged {
        fromStage := .exploring
        toStage := .drafting
      }
    ]
    check suite "invalid later payload rejects whole batch"
      (match rejected with | .error _ => true | .ok _ => false)
    let after ← IO.FS.readFile path
    check suite "invalid batch performs no partial write" (after == before)
    let afterRejected ← appendResearch context item.id {
      kind := .agent
      name := "journal-after-rejection"
      runId := ⟨"journal-after-rejection"⟩
    } #[.metadataUpdated { metadata := {
      title := item.title
      goal := "lock released"
    } }]
    check suite "validation failure releases the stream lock" afterRejected.isOk
    check suite "transaction leaves no temporary stream"
      (!(← (context.workRoot / s!".{item.id}.tmp").pathExists))
    check suite "empty batch is rejected"
      (match ← appendResearch context item.id {
        kind := .agent
        name := "journal-batch-test"
        runId := ⟨"journal-batch-test"⟩
      } #[] with | .error _ => true | .ok _ => false)

    let concurrent ← workAdd context "Concurrent batches" (some "initial") none none
    let some concurrentItem := itemOf concurrent |
      check suite "concurrency fixture created" false
    let writerCount := 12
    let tasks ← (Array.range writerCount).mapM fun index =>
      IO.asTask <| appendResearch context concurrentItem.id {
        kind := .agent
        name := s!"writer-{index}"
        runId := ⟨s!"writer-{index}"⟩
      } #[
        .metadataUpdated { metadata := {
          title := concurrentItem.title
          goal := s!"writer {index}, first"
        } },
        .metadataUpdated { metadata := {
          title := concurrentItem.title
          goal := s!"writer {index}, second"
        } }
      ]
    let mut concurrentOk := true
    for task in tasks do
      match ← IO.wait task with
      | .ok result => concurrentOk := concurrentOk && result.isOk
      | .error _ => concurrentOk := false
    check suite "concurrent journal transactions all succeed" concurrentOk
    match ← Research.readEvents context.workRoot ⟨concurrentItem.id⟩ with
    | .error message => check suite "concurrent stream validates" false message
    | .ok events =>
        check suite "concurrent stream has every event"
          (events.size == 1 + 2 * writerCount)
        check suite "concurrent sequences are contiguous"
          (events.map (·.sequence) == (Array.range events.size).map (· + 1))
        let appended := events.extract 1 events.size
        let pairsStayTogether := (Array.range writerCount).all fun index =>
          appended[2 * index]!.actor.name == appended[2 * index + 1]!.actor.name
        check suite "concurrent batches never interleave" pairsStayTogether
        let writers := (Array.range writerCount).foldl (init := ({} : Std.HashSet String))
          fun names index => names.insert appended[2 * index]!.actor.name
        check suite "every concurrent writer appears once" (writers.size == writerCount)
    check suite "concurrent commits leave no temporary stream"
      (!(← (context.workRoot / s!".{concurrentItem.id}.tmp").pathExists))

    let processFixture ← workAdd context "Process concurrency" (some "initial") none none
    let some processItem := itemOf processFixture |
      check suite "process concurrency fixture created" false
    let executable ← IO.appPath
    let processCount := 6
    let processes ← (Array.range processCount).mapM fun index => IO.asTask <| IO.Process.output {
      cmd := executable.toString
      args := #["storage-worker", context.workRoot.toString, processItem.id, s!"process-{index}"]
    }
    let mut processesOk := true
    for process in processes do
      match ← IO.wait process with
      | .ok output => processesOk := processesOk && output.exitCode == 0
      | .error _ => processesOk := false
    check suite "independent writer processes all succeed" processesOk
    match ← Research.readEvents context.workRoot ⟨processItem.id⟩ with
    | .error message => check suite "process-concurrent stream validates" false message
    | .ok events =>
        check suite "process-concurrent stream has every event"
          (events.size == 1 + 2 * processCount)
        check suite "process-concurrent sequences are contiguous"
          (events.map (·.sequence) == (Array.range events.size).map (· + 1))
        let appended := events.extract 1 events.size
        check suite "process-concurrent batches never interleave"
          ((Array.range processCount).all fun index =>
            appended[2 * index]!.actor.name == appended[2 * index + 1]!.actor.name)

def testWorkCommands (suite : Suite) (context : Context) : IO Unit :=
  withEmptyJournal context do
    check suite "empty journal lists nothing"
      (match ← workList context none with | .work items problems => items.isEmpty && problems.isEmpty | _ => false)
    let added ← workAdd context "Twin prime conjecture" (some "infinitely many") none none
    let some item := itemOf added | check suite "work add returns item" false
    check suite "new item starts exploring" (item.stage == .exploring)
    check suite "new item has zero checks" (item.attempts == 0)
    check suite "work add requires title" (failed (← workAdd context "" none none none))
    let blocked ← workSet context item.id (some "blocked") none none (some "needs lemma") none
    check suite "ordinary stage appends transition"
      (itemOf blocked |>.any fun value => value.stage == .blocked && value.note? == some "needs lemma")
    check suite "clean cannot be hand set"
      (failed (← workSet context item.id (some "clean") none none none none))
    check suite "abandon requires a recorded reason"
      (failed (← compute context ["work", "abandon", item.id]))
    check suite "abandon is explicit and retains item"
      (match ← compute context
          ["work", "abandon", item.id, "--reason", "approach exhausted"] with
        | .workAbandoned id => id == item.id
        | _ => false)
    check suite "abandoned stream still exists" (← Journal.exists? context.workRoot item.id)
    match ← Journal.read? context.workRoot item.id with
    | .error message => check suite "abandoned item materializes" false message
    | .ok abandoned => check suite "abandoned item materializes" (abandoned.stage == .abandoned)
    match ← Research.readEvents context.workRoot ⟨item.id⟩ with
    | .error message => check suite "abandonment retains history" false message
    | .ok events =>
        check suite "abandonment retains history" (events.size == 4)
        check suite "last event is abandonment"
          (match events.back!.payload with
            | .stageChanged value => value.toStage == .abandoned
            | _ => false)

def testCheckRecording (suite : Suite) (context : Context) : IO Unit :=
  withEmptyJournal context do
    let added ← workAdd context "Recording" none none none
    let some item := itemOf added | check suite "recording item created" false
    let cleanReport : DraftReport := {
      diagnostics := #[]
      hasErrors := false
      declarations := #[{
        name := `recorded
        kind := "theorem"
        type := "True"
        axioms := #[``propext]
        dependencies := #["fermat-zmod"]
        errors := #[] }]
      fatal := #[]
    }
    let first ← recordCheck context item "Draft.lean" cleanReport
    check suite "clean check derives clean stage" (first.stage == .clean)
    check suite "first check is counted" (first.attempts == 1)
    let failedReport : DraftReport := {
      diagnostics := #["Draft.lean:1:1: error"]
      hasErrors := true
      declarations := #[]
      fatal := #[]
    }
    let second ← recordCheck context first "Draft.lean" failedReport
    check suite "failed check derives drafting stage" (second.stage == .drafting)
    check suite "second check is counted" (second.attempts == 2)
    check suite "last check remains projected" (second.lastCheck?.any (!·.clean))
    match ← Research.readEvents context.workRoot ⟨item.id⟩ with
    | .error message => check suite "two checks remain in history" false message
    | .ok events =>
        let checks := events.filter fun event =>
          match event.payload with | .artifactChecked _ => true | _ => false
        check suite "two checks remain in history" (checks.size == 2)
        let outcomes := checks.map fun event =>
          match event.payload with
          | .artifactChecked value => value.clean
          | _ => false
        check suite "history keeps clean and failed outcomes"
          (match outcomes with
          | #[true, false] => true
          | _ => false)

end Frontier.Test
