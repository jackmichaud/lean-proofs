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
  initialStateId? := some ⟨"state_1"⟩
  proposition? := some "∀ n : Nat, n + 0 = n" })
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
  check suite "research event schema defaults to three" (created.schemaVersion == 3)
  let roundTrip := eventOfJson (eventJson checked)
  check suite "research JSON round trip" (match roundTrip with | .ok v => v == checked | _ => false) (reprStr roundTrip)
  let createdRoundTrip := eventOfJson (eventJson created)
  check suite "creation proposition JSON round trip" (match createdRoundTrip with
    | .ok { payload := .attemptCreated value, .. } =>
        value.proposition? == some "∀ n : Nat, n + 0 = n"
    | _ => false) (reprStr createdRoundTrip)
  let missingProposition := Json.mkObj [
    ("metadata", Json.mkObj [
      ("title", "Title"), ("goal", "Goal"), ("draftPath", .null), ("note", .null)]),
    ("initialStateId", "state_1"), ("parentAttemptId", .null)]
  check suite "creation proposition is required nullable JSON"
    (hasError (payloadOfJson "attempt.created" missingProposition) "missing field(s): proposition")
  check suite "schema version two rejected"
    (hasError (eventOfJson ((eventJson created).setObjVal! "schemaVersion" 2)) "version 2")
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
  let creationWithoutProposition := event 1 "event_1" (.attemptCreated {
    metadata
    initialStateId? := some ⟨"state_1"⟩ })
  check suite "initial state requires proposition" (hasError
    (validateStream ⟨"attempt_1"⟩ #[creationWithoutProposition]) "both be present")
  let creationWithoutState := event 1 "event_1" (.attemptCreated {
    metadata
    proposition? := some "True" })
  check suite "proposition requires initial state" (hasError
    (validateStream ⟨"attempt_1"⟩ #[creationWithoutState]) "both be present")
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
  let proposal1 := event 2 "event_2" (.actionProposed {
    stateId := ⟨"state_1"⟩
    action := "intro n" })
  let step1 := event 3 "event_3" (.actionEvaluated {
    transitionId := ⟨"transition_1"⟩
    parentStateId := ⟨"state_1"⟩
    childStateId? := some ⟨"state_2"⟩
    action := "intro n"
    outcome := .accepted
    goals := #["n + 0 = n"] })
  let proposal2 := event 4 "event_4" (.actionProposed {
    stateId := ⟨"state_2"⟩
    action := "simp" })
  let step2 := event 5 "event_5" (.actionEvaluated {
    transitionId := ⟨"transition_2"⟩
    parentStateId := ⟨"state_2"⟩
    childStateId? := some ⟨"state_3"⟩
    action := "simp"
    outcome := .accepted
    complete := true })
  let proofEvents := #[created, proposal1, step1, proposal2, step2]
  let plan := replayPlan ⟨"attempt_1"⟩ proofEvents ⟨"state_3"⟩
  check suite "replay plan follows accepted lineage in order" (match plan with
    | .ok value =>
        value.proposition == "∀ n : Nat, n + 0 = n" &&
        value.initialStateId == ⟨"state_1"⟩ && value.targetStateId == ⟨"state_3"⟩ &&
        value.transitions.size == 2 &&
        value.transitions[0]!.parentStateId == ⟨"state_1"⟩ &&
        value.transitions[0]!.childStateId == ⟨"state_2"⟩ &&
        value.transitions[0]!.action == "intro n" &&
        value.transitions[0]!.goals == #["n + 0 = n"] && !value.transitions[0]!.complete &&
        value.transitions[1]!.parentStateId == ⟨"state_2"⟩ &&
        value.transitions[1]!.childStateId == ⟨"state_3"⟩ &&
        value.transitions[1]!.action == "simp" && value.transitions[1]!.complete
    | _ => false) (reprStr plan)
  let noProofCreated := event 1 "event_1" (.attemptCreated { metadata })
  check suite "replay rejects attempt without proposition" (hasError
    (replayPlan ⟨"attempt_1"⟩ #[noProofCreated] ⟨"state_1"⟩) "no proposition")
  check suite "replay rejects unknown target" (hasError
    (replayPlan ⟨"attempt_1"⟩ #[created, proposal1, step1] ⟨"state_missing"⟩) "unknown or unreachable")
  check suite "evaluation requires an adjacent proposal" (hasError
    (validateStream ⟨"attempt_1"⟩ #[created, { step1 with sequence := 2, eventId := ⟨"event_2"⟩ }])
    "immediately follow")
  let mismatched := { step1 with payload := match step1.payload with
    | .actionEvaluated value => .actionEvaluated { value with action := "simp" }
    | payload => payload }
  check suite "evaluation must match its proposal" (hasError
    (validateStream ⟨"attempt_1"⟩ #[created, proposal1, mismatched]) "does not match")
  let abandoned := event 2 "event_2" (.branchAbandoned {
    stateId := ⟨"state_1"⟩
    reason := "superseded" })
  let afterAbandoned := event 3 "event_3" (.actionProposed {
    stateId := ⟨"state_1"⟩
    action := "simp" })
  check suite "abandoned proof states cannot be extended" (hasError
    (validateStream ⟨"attempt_1"⟩ #[created, abandoned, afterAbandoned]) "cannot be extended")
  let afterCompleteProposal := event 6 "event_6" (.actionProposed {
    stateId := ⟨"state_3"⟩
    action := "rfl" })
  let afterComplete := event 7 "event_7" (.actionEvaluated {
    transitionId := ⟨"transition_3"⟩
    parentStateId := ⟨"state_3"⟩
    childStateId? := some ⟨"state_4"⟩
    action := "rfl"
    outcome := .accepted
    complete := true })
  check suite "replay rejects malformed completed lineage" (hasError
    (replayPlan ⟨"attempt_1"⟩ (proofEvents ++ #[afterCompleteProposal, afterComplete]) ⟨"state_4"⟩)
    "malformed replay lineage")
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
