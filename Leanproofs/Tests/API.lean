/-
Copyright (c) 2026 Jack Michaud. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Michaud
-/

import Leanproofs.Tests.Support

/-!
# Typed agent API tests
-/

open Lean Frontier Frontier.CLI

namespace Frontier.Test

private def fieldString? (json : Json) (key : String) : Option String :=
  (json.getObjVal? key >>= Json.getStr?).toOption

private def errorCode? (json : Json) : Option String := do
  let error ← json.getObjVal? "error" |>.toOption
  fieldString? error "code"

private def result? (json : Json) : Option Json :=
  json.getObjVal? "result" |>.toOption

private def mkRequest (operation : String) (params : Json) (requestId := "req-1")
    (attemptId? : Option String := none) : API.Request := {
  apiVersion := API.version
  requestId
  operation
  environment? := none
  attemptId? := attemptId?.map (⟨·⟩)
  params
  actor := {
    kind := .agent
    name := "test-agent"
    runId := ⟨"api-test-run"⟩
    model? := some "test-model"
  }
}

private def actionResult? (response : Json) (id : String) : Option Json := do
  let result ← result? response
  let values ← (result.getObjVal? "results" >>= Json.getArr?).toOption
  values.find? fun value => fieldString? value "actionId" == some id

def testAPI (suite : Suite) (context : Context) : IO Unit := do
  let context := { context with session := true }
  let attemptId := "api-test-attempt"
  let attemptPath := context.workRoot / s!"{attemptId}.jsonl"
  let otherAttemptId := "api-other-attempt"
  let otherAttemptPath := context.workRoot / s!"{otherAttemptId}.jsonl"
  if ← attemptPath.pathExists then IO.FS.removeFile attemptPath
  if ← otherAttemptPath.pathExists then IO.FS.removeFile otherAttemptPath
  let source :=
    "{\"apiVersion\":\"frontier.agent/v1\",\"requestId\":\"req-1\"," ++
    "\"operation\":\"capabilities.get\",\"params\":{}," ++
    "\"provenance\":{\"kind\":\"agent\",\"name\":\"test-agent\",\"runId\":\"api-test-run\"}}"
  let parsed := API.parseRequest source
  check suite "a typed request envelope parses"
    (parsed.toOption.map (·.requestId) == some "req-1")
  check suite "typed params must be an object"
    ((API.parseRequest (source.replace "\"params\":{}" "\"params\":[]")).toOption.isNone)
  check suite "correlation fields survive a structural decoding error"
    (API.requestMetadata (source.replace "\"params\":{}" "\"params\":[]")
      == (some "req-1", some "capabilities.get"))
  check suite "typed provenance is required"
    ((API.parseRequest
      (source.replace ",\"provenance\":{\"kind\":\"agent\",\"name\":\"test-agent\",\"runId\":\"api-test-run\"}" "")).toOption.isNone)

  let arrayResponse ← handleRequest context "[\"policy\"]"
  check suite "serve rejects legacy array requests"
    (errorCode? arrayResponse == some "INVALID_REQUEST")
  let bareResponse ← handleRequest context "policy"
  check suite "serve rejects bare command requests"
    (errorCode? bareResponse == some "INVALID_REQUEST")

  let request := parsed.toOption.get!
  let capabilities ← computeTyped context request
  check suite "capabilities preserve the request id"
    (fieldString? capabilities "requestId" == some "req-1")
  check suite "capabilities use the loaded environment"
    (fieldString? capabilities "environment" == some (API.environmentId context))
  check suite "capabilities succeed"
    ((capabilities.getObjValAs? Bool "ok").toOption == some true)
  check suite "capabilities describe operation contracts"
    ((result? capabilities >>= fun result =>
      (result.getObjVal? "contracts" >>= Json.getArr?).toOption).any (·.size == 10))

  let unsupported := { request with operation := "cli.execute" }
  let unsupportedResponse ← computeTyped context unsupported
  check suite "unsupported typed operations fail explicitly"
    ((unsupportedResponse.getObjValAs? Bool "ok").toOption == some false
      && errorCode? unsupportedResponse == some "UNSUPPORTED_OPERATION")

  let wrongVersion := { request with apiVersion := "frontier.agent/v999" }
  let wrongVersionResponse ← computeTyped context wrongVersion
  check suite "unsupported versions have a stable error code"
    (errorCode? wrongVersionResponse == some "UNSUPPORTED_API_VERSION")

  let wrongEnvironment := { request with environment? := some "not-the-loaded-environment" }
  let wrongEnvironmentResponse ← computeTyped context wrongEnvironment
  check suite "environment pinning rejects a mismatch"
    (errorCode? wrongEnvironmentResponse == some "ENVIRONMENT_MISMATCH")

  let malformedSearch ← computeTyped context (mkRequest "declarations.search"
    (Json.mkObj [("query", toJson "Nat"), ("limit", toJson "many")]))
  check suite "operation params are type checked"
    (errorCode? malformedSearch == some "INVALID_PARAMS")
  let extraSearch ← computeTyped context (mkRequest "declarations.search"
    (Json.mkObj [("query", toJson "Nat"), ("surprise", toJson true)]))
  check suite "operation params reject unknown fields"
    (errorCode? extraSearch == some "INVALID_PARAMS")

  let search ← computeTyped context (mkRequest "declarations.search"
    (Json.mkObj [("query", toJson "Nat.add_comm"), ("limit", toJson (3 : Nat))]))
  check suite "declaration search is a native typed operation"
    ((search.getObjValAs? Bool "ok").toOption == some true)

  let created ← computeTyped context (mkRequest "research.attempt.create" (Json.mkObj [
    ("title", toJson "API proof attempt"),
    ("goal", toJson "Prove the additive identity"),
    ("proposition", toJson "∀ n : ℕ, n + 0 = n")]) "create-1" (some attemptId))
  check suite "agents can create a durable proof attempt"
    ((created.getObjValAs? Bool "ok").toOption == some true)
  let some createdResult := result? created
    | check suite "attempt creation returns a result" false
  let some initialProof := createdResult.getObjVal? "initialProofState" |>.toOption
    | check suite "attempt creation returns an initial proof state" false
  let some initialStateId := fieldString? initialProof "stateId"
    | check suite "initial proof state has a durable id" false
  check suite "initial proof state uses the attempt root id" (initialStateId == "root")

  let attempts ← computeTyped context (mkRequest "research.attempt.list" (Json.mkObj []))
  check suite "typed clients can list durable attempts"
    ((result? attempts >>= fun result =>
      (result.getObjVal? "attempts" >>= Json.getArr?).toOption).any (·.size == 1))
  let attempt ← computeTyped context
    (mkRequest "research.attempt.get" (Json.mkObj []) "get-1" (some attemptId))
  check suite "typed clients can resume from complete attempt history"
    ((result? attempt >>= fun result =>
      (result.getObjVal? "events" >>= Json.getArr?).toOption).any (·.size == 1))

  let premises ← computeTyped context (mkRequest "premises.retrieve"
    (Json.mkObj [("goal", toJson "∀ n : ℕ, n + 0 = n"),
      ("retrievalId", toJson "retrieval-1"), ("limit", toJson (3 : Nat))])
    "premises-1" (some attemptId))
  check suite "premise retrieval accepts a Lean goal"
    ((premises.getObjValAs? Bool "ok").toOption == some true)
  let badGoal ← computeTyped context (mkRequest "premises.retrieve"
    (Json.mkObj [("goal", toJson "not valid Lean !!!"),
      ("retrievalId", toJson "retrieval-bad")]) "premises-bad" (some attemptId))
  check suite "invalid Lean goals have a stable error code"
    (errorCode? badGoal == some "INVALID_GOAL")

  let detachedPremises ← computeTyped context (mkRequest "premises.retrieve"
    (Json.mkObj [("goal", toJson "True"), ("retrievalId", toJson "detached")]))
  check suite "research operations require an attempt id"
    (errorCode? detachedPremises == some "INVALID_PARAMS")

  let batchParams := Json.mkObj [
    ("parentStateId", toJson initialStateId),
    ("actions", Json.arr #[
      Json.mkObj [("id", toJson "advance"), ("tactic", toJson "intro n"),
        ("transitionId", toJson "transition-advance"),
        ("retrievalIds", toJson #["retrieval-1"])],
      Json.mkObj [("id", toJson "reject"), ("tactic", toJson "exact nonsense_lemma"),
        ("transitionId", toJson "transition-reject")],
      Json.mkObj [("id", toJson "finish"), ("tactic", toJson "simp"),
        ("transitionId", toJson "transition-finish")]])]
  let batch ← computeTyped context
    (mkRequest "proof.evaluateBatch" batchParams "batch-1" (some attemptId))
  check suite "batch responses preserve request correlation"
    (fieldString? batch "requestId" == some "batch-1")
  check suite "an accepted batch sibling advances independently"
    ((actionResult? batch "advance" >>= fun value => fieldString? value "outcome")
      == some "accepted")
  check suite "a rejected batch sibling does not abort the batch"
    ((actionResult? batch "reject" >>= fun value => fieldString? value "outcome")
      == some "rejected")
  check suite "a later batch sibling can still complete"
    ((actionResult? batch "finish" >>= fun value => fieldString? value "outcome")
      == some "complete")

  let beforeInvalid ← Research.readEvents context.workRoot ⟨attemptId⟩
  let invalidHistory ← computeTyped context (mkRequest "proof.evaluateBatch" (Json.mkObj [
    ("parentStateId", toJson initialStateId),
    ("actions", Json.arr #[Json.mkObj [
      ("id", toJson "bad-reference"), ("tactic", toJson "simp"),
      ("transitionId", toJson "transition-bad-reference"),
      ("retrievalIds", toJson #["missing-retrieval"]) ]])])
    "batch-invalid-history" (some attemptId))
  check suite "invalid research references reject the whole batch"
    (errorCode? invalidHistory == some "RESEARCH_STATE_ERROR")
  let afterInvalid ← Research.readEvents context.workRoot ⟨attemptId⟩
  check suite "a rejected event batch leaves no partial history"
    (beforeInvalid.toOption.map (·.size) == afterInvalid.toOption.map (·.size))

  let zeroHeartbeats ← computeTyped context (mkRequest "proof.evaluateBatch"
    (Json.mergeObj batchParams (Json.mkObj [("heartbeats", toJson (0 : Nat))]))
    "batch-zero" (some attemptId))
  check suite "sessions reject unbounded tactic evaluation"
    (errorCode? zeroHeartbeats == some "INVALID_PARAMS")

  let otherCreated ← computeTyped context (mkRequest "research.attempt.create" (Json.mkObj [
    ("title", toJson "Arithmetic policy attempt"),
    ("goal", toJson "Check the policy boundary"),
    ("proposition", toJson "(2 : ℕ) + 2 = 4")])
    "create-other" (some otherAttemptId))
  check suite "a second proof attempt can be recorded"
    ((otherCreated.getObjValAs? Bool "ok").toOption == some true)
  let some otherResult := result? otherCreated
    | check suite "second attempt creation returns a result" false
  let some otherProof := otherResult.getObjVal? "initialProofState" |>.toOption
    | check suite "second attempt returns an initial proof state" false
  let some arithmeticStateId := fieldString? otherProof "stateId"
    | check suite "second initial proof state has a durable id" false
  let policyBatch ← computeTyped context (mkRequest "proof.evaluateBatch" (Json.mkObj [
    ("parentStateId", toJson arithmeticStateId),
    ("actions", Json.arr #[
      Json.mkObj [("id", toJson "forbidden"), ("tactic", toJson "native_decide"),
        ("transitionId", toJson "transition-forbidden")],
      Json.mkObj [("id", toJson "trusted"), ("tactic", toJson "simp"),
        ("transitionId", toJson "transition-trusted")]])])
    "batch-2" (some otherAttemptId))
  check suite "policy-invalid proofs are rejected explicitly"
    ((actionResult? policyBatch "forbidden" >>= fun value => fieldString? value "outcome")
      == some "policyRejected")
  check suite "policy rejection does not block a trusted sibling"
    ((actionResult? policyBatch "trusted" >>= fun value => fieldString? value "outcome")
      == some "complete")

  let some advance := actionResult? batch "advance"
    | check suite "accepted actions return inspectable states" false
  let some stateId := fieldString? advance "stateId"
    | check suite "accepted actions return durable state ids" false
  check suite "child state ids derive from durable transition ids"
    (stateId == "after-transition-advance")
  let inspected ← computeTyped context (mkRequest "proof.inspectState"
    (Json.mkObj [("stateId", toJson stateId)]) "inspect-1" (some attemptId))
  check suite "stored proof states can be inspected"
    ((inspected.getObjValAs? Bool "ok").toOption == some true)

  let wrongOwner ← computeTyped context (mkRequest "proof.inspectState"
    (Json.mkObj [("stateId", toJson stateId)]) "inspect-wrong-owner" (some otherAttemptId))
  check suite "proof states cannot cross attempt boundaries"
    (errorCode? wrongOwner == some "RESEARCH_STATE_ERROR")

  let restarted : Context := { context with
    proofStatesRef := ← IO.mkRef ({}, 1)
    researchProofStatesRef := ← IO.mkRef {}
  }
  let missingAfterRestart ← computeTyped restarted (mkRequest "proof.inspectState"
    (Json.mkObj [("stateId", toJson stateId)]) "inspect-after-restart" (some attemptId))
  check suite "durable history is distinct from a live state"
    (errorCode? missingAfterRestart == some "STATE_NOT_FOUND")
  let originalStream ← IO.FS.readFile attemptPath
  let parsedEvents ← Research.readEvents context.workRoot ⟨attemptId⟩
  let tamperedEvents := parsedEvents.toOption.getD #[] |>.map fun event =>
    match event.payload with
    | .actionEvaluated value =>
        if value.childStateId? == some ⟨stateId⟩ then
          { event with payload := .actionEvaluated { value with goals := #["tampered goal"] } }
        else event
    | _ => event
  IO.FS.writeFile attemptPath
    ("\n".intercalate (tamperedEvents.map (Research.eventJson · |>.compress)).toList ++ "\n")
  let divergent ← computeTyped restarted (mkRequest "proof.rehydrate"
    (Json.mkObj [("stateId", toJson stateId)]) "rehydrate-drift" (some attemptId))
  check suite "rehydration rejects recorded goal drift"
    (errorCode? divergent == some "REPLAY_DIVERGED")
  check suite "failed rehydration installs no live binding"
    ((← restarted.researchProofStatesRef.get).isEmpty)
  IO.FS.writeFile attemptPath originalStream
  let rehydrated ← computeTyped restarted (mkRequest "proof.rehydrate"
    (Json.mkObj [("stateId", toJson stateId)]) "rehydrate-1" (some attemptId))
  check suite "a fresh session can rehydrate a recorded branch"
    ((rehydrated.getObjValAs? Bool "ok").toOption == some true &&
      (result? rehydrated >>= fun value => fieldString? value "stateId") == some stateId)
  check suite "rehydration reports verified history"
    ((result? rehydrated >>= fun value => value.getObjValAs? Bool "replayMatchedHistory" |>.toOption)
      == some true)
  let continued ← computeTyped restarted (mkRequest "proof.evaluateBatch" (Json.mkObj [
    ("parentStateId", toJson stateId),
    ("actions", Json.arr #[Json.mkObj [
      ("id", toJson "continue"), ("tactic", toJson "simp"),
      ("transitionId", toJson "transition-after-restart")]])])
    "batch-after-restart" (some attemptId))
  check suite "proof search continues from a rehydrated state"
    ((actionResult? continued "continue" >>= fun value => fieldString? value "outcome")
      == some "complete")

  match ← Research.readEvents context.workRoot ⟨attemptId⟩ with
  | .error message => check suite "agent activity has a valid event stream" false message
  | .ok events =>
      check suite "premise retrieval is recorded"
        (events.any fun event => match event.payload with
          | .retrievalPerformed value => value.retrievalId == ⟨"retrieval-1"⟩
          | _ => false)
      check suite "batch actions and evaluations are recorded"
        ((events.filter fun event => match event.payload with
          | .actionProposed _ | .actionEvaluated _ => true
          | _ => false).size == 8)
      check suite "agent provenance reaches durable events"
        (events.all fun event => event.actor.name == "test-agent" && event.actor.model? == some "test-model")
  if ← attemptPath.pathExists then IO.FS.removeFile attemptPath
  if ← otherAttemptPath.pathExists then IO.FS.removeFile otherAttemptPath

end Frontier.Test
