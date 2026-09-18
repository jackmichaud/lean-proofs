/-
Copyright (c) 2026 Jack Michaud. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Michaud
-/

import Leanproofs.Tests.Support

/-!
# Typed agent API tests

Kept callable independently while the additive API settles; the main runner can adopt
`testAPI` without changing this module.
-/

open Lean Frontier Frontier.CLI

namespace Frontier.Test

private def fieldString? (json : Json) (key : String) : Option String :=
  (json.getObjVal? key >>= Json.getStr?).toOption

private def errorCode? (json : Json) : Option String := do
  let error ← json.getObjVal? "error" |>.toOption
  fieldString? error "code"

def testAPI (suite : Suite) (context : Context) : IO Unit := do
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

  -- The original array parser remains the compatibility contract.
  check suite "legacy arrays still preserve argument boundaries"
    ((parseRequest "[\"suggest\",\"--goal\",\"a b c\"]").toOption
      == some ["suggest", "--goal", "a b c"])

  let request := parsed.toOption.get!
  let capabilities ← computeTyped context request
  check suite "capabilities preserve the request id"
    (fieldString? capabilities "requestId" == some "req-1")
  check suite "capabilities use the loaded environment"
    (fieldString? capabilities "environment" == some (API.environmentId context))
  check suite "capabilities succeed"
    ((capabilities.getObjValAs? Bool "ok").toOption == some true)

  let unsupported := { request with operation := "proof.evaluateBatch" }
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

  let cliRequest := { request with
    operation := "cli.execute"
    params := Json.mkObj [("args", toJson #["policy"])]
  }
  let cliResponse ← computeTyped context cliRequest
  check suite "the typed compatibility operation routes through compute"
    ((cliResponse.getObjValAs? Bool "ok").toOption == some true)

  let failedCli := { cliRequest with params := Json.mkObj [("args", toJson #["unknown"])] }
  let failedCliResponse ← computeTyped context failedCli
  check suite "legacy command failures remain failures in the typed envelope"
    (errorCode? failedCliResponse == some "COMMAND_FAILED")

end Frontier.Test
