/- Copyright (c) 2026 Jack Michaud. All rights reserved. -/
import Leanproofs.Research.Events
import Leanproofs.Tests.Support

open Lean Frontier.Research
namespace Frontier.Test

private def env : EnvironmentFingerprint := {
  leanVersion := "4.test"
  mathlibRevision := "mathlib-test"
  frontierRevision := "frontier-test"
  importsHash := "imports-test"
  policyVersion := "policy-test" }
private def actor : Actor := {
  kind := .agent
  name := "test-agent"
  runId := ⟨"run_1"⟩ }
private def event (n : Nat) (id : String) (payload : Payload) : Event := {
  eventId := ⟨id⟩
  attemptId := ⟨"attempt_1"⟩
  sequence := n
  occurredAt := s!"2026-09-18T00:00:0{n}Z"
  environment := env
  actor
  payload }
private def metadata : WorkMetadata := {
  title := "Research test"
  goal := "forall n, n + 0 = n"
  draftPath? := some "Draft.lean"
  note? := some "first approach" }
private def created := event 1 "event_1" (.attemptCreated {
  metadata
  initialStateId? := some ⟨"state_1"⟩ })
private def checked := event 2 "event_2" (.artifactChecked {
  artifact := "Draft.lean"
  clean := true
  declarations := 1
  reuses := #["catalog.result"]
  axioms := #["propext"]
  diagnostics := #["note"] })
private def promoted := event 3 "event_3" (.artifactPromoted {
  artifact := "Draft.lean"
  catalogId := "result-1" })
private def hasError (result : Except String α) (fragment : String) : Bool :=
  match result with | .error message => message.contains fragment | .ok _ => false
private def withRoot (action : System.FilePath → IO Unit) : IO Unit := do
  let root : System.FilePath := "build" / "test-research-events"
  IO.FS.createDirAll root
  for entry in ← root.readDir do if entry.fileName.endsWith ".jsonl" then IO.FS.removeFile entry.path
  action root

def testResearchEvents (suite : Suite) : IO Unit := do
  let roundTrip := eventOfJson (eventJson checked)
  check suite "research JSON round trip" (match roundTrip with | .ok v => v == checked | _ => false) (reprStr roundTrip)
  check suite "unknown fields rejected" (hasError (eventOfJson ((eventJson checked).setObjVal! "extra" true)) "unexpected field")
  check suite "trusted history rejected" (hasError (eventOfJson ((eventJson checked).setObjVal! "trusted" true)) "trusted=false")
  check suite "path traversal rejected" (hasError (streamPath "build" ⟨"../escape"⟩) "invalid attempt id")
  check suite "invalid calendar timestamp rejected" (hasError (validateTimestamp "2026-02-30T00:00:00Z") "invalid UTC timestamp")
  check suite "sequence gaps rejected" (hasError (validateStream ⟨"attempt_1"⟩ #[created, { checked with sequence := 3 }]) "expected 2")
  check suite "creation must be first" (hasError (validateStream ⟨"attempt_1"⟩ #[{ checked with sequence := 1 }]) "first event")
  check suite "timestamps monotonic" (hasError (validateStream ⟨"attempt_1"⟩ #[created,
    { checked with occurredAt := "2026-09-17T00:00:00Z" }]) "precedes")
  let revisedEnvironment := { checked with environment := { env with policyVersion := "other" } }
  check suite "attempt may span environments"
    (validateStream ⟨"attempt_1"⟩ #[created, revisedEnvironment] |>.isOk)
  check suite "unknown state rejected" (hasError (validateStream ⟨"attempt_1"⟩ #[created,
    event 2 "event_2" (.actionProposed {
      stateId := ⟨"missing"⟩
      action := "simp" })]) "unknown proof state")
  check suite "derived clean stage protected" (hasError (validateStream ⟨"attempt_1"⟩ #[created,
    event 2 "event_2" (.stageChanged {
      fromStage := .drafting
      toStage := .clean })]) "derived")
  check suite "promotion requires clean" (hasError (validateStream ⟨"attempt_1"⟩ #[created,
    { promoted with
      sequence := 2
      eventId := ⟨"event_2"⟩ }]) "only a clean attempt")
  let updated := event 2 "event_2" (.metadataUpdated { metadata := {
    title := "Retitled"
    goal := "new goal"
    draftPath? := none
    note? := none } })
  let view := materialize ⟨"attempt_1"⟩ #[created, updated]
  check suite "metadata snapshots clear fields" (match view with
    | .ok v => v.title == "Retitled" && v.draftPath?.isNone && v.note?.isNone | _ => false) (reprStr view)
  withRoot fun root => do
    let a ← appendEvent root ⟨"attempt_1"⟩ created
    let b ← appendEvent root ⟨"attempt_1"⟩ checked
    let c ← appendEvent root ⟨"attempt_1"⟩ promoted
    check suite "append succeeds" (a.isOk && b.isOk && c.isOk)
    let duplicate ← appendEvent root ⟨"attempt_1"⟩ promoted
    check suite "nonmonotonic append rejected" (hasError duplicate "expected 4")
    let summary ← readSummary root ⟨"attempt_1"⟩
    check suite "summary covers work state" (match summary with
      | .ok v => v.title == metadata.title && v.goal == metadata.goal && v.draftPath? == some "Draft.lean" &&
          v.note? == metadata.note? && v.stage == .registered && v.artifactChecks == 1 &&
          v.lastCheck?.map (fun x => x.reuses) == some #["catalog.result"] &&
          v.lastCheck?.map (fun x => x.axioms) == some #["propext"] &&
          v.promotedCatalogId? == some "result-1" && !v.trusted | _ => false) (reprStr summary)
    let listed ← listSummaries root
    check suite "streams list as summaries" (match listed with
      | .ok values => values.size == 1 && values[0]!.attemptId == ⟨"attempt_1"⟩ | _ => false) (reprStr listed)

end Frontier.Test
