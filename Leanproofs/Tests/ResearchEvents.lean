/-
Copyright (c) 2026 Jack Michaud. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Michaud
-/

import Leanproofs.Research.Events
import Leanproofs.Tests.Support

open Lean Frontier.Research

namespace Frontier.Test

private def fixtureEnvironment : EnvironmentFingerprint := {
  leanVersion := "4.test", mathlibRevision := "mathlib-test", frontierRevision := "frontier-test"
  importsHash := "imports-test", policyVersion := "policy-test"
}

private def fixtureActor : Actor := {
  kind := .agent, name := "test-agent", runId := ⟨"run_1"⟩, model? := some "test-model"
}

private def event (sequence : Nat) (id : String) (payload : Payload) : Event := {
  eventId := ⟨id⟩, attemptId := ⟨"attempt_1"⟩, sequence
  occurredAt := s!"2026-09-18T00:00:0{sequence}Z"
  environment := fixtureEnvironment, actor := fixtureActor, payload
}

private def created : Event := event 1 "event_1" (.attemptCreated {
  title := "Research test", goal := "forall n, n + 0 = n", initialStateId? := some ⟨"state_1"⟩
})

private def checked : Event := event 2 "event_2" (.artifactChecked {
  artifact := "Draft.lean", clean := false, declarations := 1
  errors := #["policy error"], diagnostics := #["diagnostic"]
})

private def withRoot (action : System.FilePath → IO Unit) : IO Unit := do
  let root : System.FilePath := "build" / "test-research-events"
  IO.FS.createDirAll root
  for entry in ← root.readDir do
    if entry.fileName.endsWith ".jsonl" then IO.FS.removeFile entry.path
  action root

/-- Callable independently; intentionally not wired into the legacy aggregate test runner. -/
def testResearchEvents (suite : Suite) : IO Unit := do
  let roundTrip := eventOfJson (eventJson checked)
  check suite "strict research-event JSON round trip" (match roundTrip with
    | .ok value => value == checked | .error _ => false) (reprStr roundTrip)

  let withUnknown := (eventJson checked).setObjVal! "surprise" (toJson true)
  check suite "unknown research-event fields are rejected" (match eventOfJson withUnknown with
    | .error message => message.contains "unexpected field"
    | _ => false)

  let falselyTrusted := (eventJson checked).setObjVal! "trusted" (toJson true)
  check suite "research events cannot claim trust" (match eventOfJson falselyTrusted with
    | .error message => message.contains "trusted=false"
    | _ => false)

  check suite "research-event path traversal is rejected" (match streamPath "build" ⟨"../escape"⟩ with
    | .error _ => true | _ => false)

  check suite "research-event sequence gaps are rejected" (match validateStream ⟨"attempt_1"⟩ #[created, { checked with sequence := 3 }] with
    | .error message => message.contains "expected 2" | _ => false)

  check suite "the first research event creates the attempt" (match validateStream ⟨"attempt_1"⟩ #[{ checked with sequence := 1 }] with
    | .error message => message.contains "first event" | _ => false)

  withRoot fun root => do
    let first ← appendEvent root ⟨"attempt_1"⟩ created
    let second ← appendEvent root ⟨"attempt_1"⟩ checked
    check suite "research-event append succeeds" (match first, second with
      | .ok _, .ok _ => true | _, _ => false)
    let duplicate ← appendEvent root ⟨"attempt_1"⟩ checked
    check suite "non-monotonic research-event append is rejected" (match duplicate with
      | .error message => message.contains "expected 3" | _ => false)
    let loaded ← readEvents root ⟨"attempt_1"⟩
    check suite "stored research events read back" (match loaded with
      | .ok value => value == #[created, checked] | .error _ => false) (reprStr loaded)
    let summary ← readSummary root ⟨"attempt_1"⟩
    check suite "research summary tracks the latest check" (match summary with
      | .ok value => value.eventCount == 2 && value.lastCheckAt? == some checked.occurredAt &&
          value.artifactChecks == 1 && value.lastCheck?.map (·.clean) == some false && !value.trusted
      | _ => false) (reprStr summary)
end Frontier.Test
