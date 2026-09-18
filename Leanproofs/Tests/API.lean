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

private def mkRequest (operation : String) (params : Json) (requestId := "req-1") : API.Request := {
  apiVersion := API.version
  requestId
  operation
  environment? := none
  params
  provenance := Json.mkObj [("actor", toJson "test")]
}

private def actionResult? (response : Json) (id : String) : Option Json := do
  let result ← result? response
  let values ← (result.getObjVal? "results" >>= Json.getArr?).toOption
  values.find? fun value => fieldString? value "actionId" == some id

def testAPI (suite : Suite) (context : Context) : IO Unit := do
  let context := { context with session := true }
  let source :=
    "{\"apiVersion\":\"frontier.agent/v1\",\"requestId\":\"req-1\"," ++
    "\"operation\":\"capabilities.get\",\"params\":{},\"provenance\":{\"actor\":\"test\"}}"
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
      (source.replace ",\"provenance\":{\"actor\":\"test\"}" "")).toOption.isNone)

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

  let premises ← computeTyped context (mkRequest "premises.retrieve"
    (Json.mkObj [("goal", toJson "∀ n : ℕ, n + 0 = n"), ("limit", toJson (3 : Nat))]))
  check suite "premise retrieval accepts a Lean goal"
    ((premises.getObjValAs? Bool "ok").toOption == some true)
  let badGoal ← computeTyped context (mkRequest "premises.retrieve"
    (Json.mkObj [("goal", toJson "not valid Lean !!!")]))
  check suite "invalid Lean goals have a stable error code"
    (errorCode? badGoal == some "INVALID_GOAL")

  let batchParams := Json.mkObj [
    ("goal", toJson "∀ n : ℕ, n + 0 = n"),
    ("actions", Json.arr #[
      Json.mkObj [("id", toJson "advance"), ("tactic", toJson "intro n")],
      Json.mkObj [("id", toJson "reject"), ("tactic", toJson "exact nonsense_lemma")],
      Json.mkObj [("id", toJson "finish"), ("tactic", toJson "simp")]])]
  let batch ← computeTyped context (mkRequest "proof.evaluateBatch" batchParams "batch-1")
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

  let zeroHeartbeats ← computeTyped context (mkRequest "proof.evaluateBatch"
    (Json.mergeObj batchParams (Json.mkObj [("heartbeats", toJson (0 : Nat))])))
  check suite "sessions reject unbounded tactic evaluation"
    (errorCode? zeroHeartbeats == some "INVALID_PARAMS")

  let policyBatch ← computeTyped context (mkRequest "proof.evaluateBatch" (Json.mkObj [
    ("goal", toJson "(2 : ℕ) + 2 = 4"),
    ("actions", Json.arr #[
      Json.mkObj [("id", toJson "forbidden"), ("tactic", toJson "native_decide")],
      Json.mkObj [("id", toJson "trusted"), ("tactic", toJson "decide")]])]))
  check suite "policy-invalid proofs are rejected explicitly"
    ((actionResult? policyBatch "forbidden" >>= fun value => fieldString? value "outcome")
      == some "policyRejected")
  check suite "policy rejection does not block a trusted sibling"
    ((actionResult? policyBatch "trusted" >>= fun value => fieldString? value "outcome")
      == some "complete")

  let some advance := actionResult? batch "advance"
    | check suite "accepted actions return inspectable states" false
  let some stateId := (advance.getObjVal? "stateId" >>= Json.getNat?).toOption
    | check suite "accepted actions return numeric state ids" false
  let inspected ← computeTyped context (mkRequest "proof.inspectState"
    (Json.mkObj [("stateId", toJson stateId)]))
  check suite "stored proof states can be inspected"
    ((inspected.getObjValAs? Bool "ok").toOption == some true)

end Frontier.Test
