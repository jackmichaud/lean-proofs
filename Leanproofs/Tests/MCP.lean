/-
Copyright (c) 2026 Jack Michaud. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Michaud
-/

import Leanproofs.Tests.Support
import Leanproofs.Frontier.MCP

/-! # MCP adapter tests -/

open Lean Frontier Frontier.CLI

namespace Frontier.Test

private def field? (json : Json) (key : String) : Option Json :=
  json.getObjVal? key |>.toOption

private def errorCode? (json : Json) : Option Json := do
  let error ← field? json "error"
  field? error "code"

private def responseResult? (json : Json) : Option Json :=
  field? json "result"

private def initializedRequest (version := MCP.protocolVersion) : Json := Json.mkObj [
  ("jsonrpc", toJson "2.0"),
  ("id", toJson (1 : Nat)),
  ("method", toJson "initialize"),
  ("params", Json.mkObj [
    ("protocolVersion", toJson version),
    ("capabilities", Json.mkObj []),
    ("clientInfo", Json.mkObj [("name", toJson "mcp-test-client"),
      ("version", toJson "1.0")])])]

private def readySession (context : Context) : IO MCP.Session := do
  let (initialized, _) ← MCP.handleMessage context MCP.initialSession initializedRequest
  let notification := Json.mkObj [
    ("jsonrpc", toJson "2.0"), ("method", toJson "notifications/initialized")]
  return (← MCP.handleMessage context initialized notification).1

def testMCP (suite : Suite) (context : Context) : IO Unit := do
  let context := { context with session := true }

  let (_, parseReply?) ← MCP.handleLine context MCP.initialSession "{broken"
  check suite "MCP malformed JSON returns parse error"
    (parseReply?.bind errorCode? == some (toJson (-32700 : Int)))

  let (_, arrayReply?) ← MCP.handleMessage context MCP.initialSession (Json.arr #[])
  check suite "MCP rejects JSON-RPC batches"
    (arrayReply?.bind errorCode? == some (toJson (-32600 : Int)))

  let ping := Json.mkObj [("jsonrpc", toJson "2.0"), ("id", toJson "ping-id"),
    ("method", toJson "ping")]
  let (_, pingReply?) ← MCP.handleMessage context MCP.initialSession ping
  check suite "MCP ping works before initialization"
    ((pingReply?.bind (field? · "id")) == some (toJson "ping-id"))

  let beforeReady := Json.mkObj [("jsonrpc", toJson "2.0"), ("id", toJson (2 : Nat)),
    ("method", toJson "tools/list")]
  let (_, beforeReadyReply?) ← MCP.handleMessage context MCP.initialSession beforeReady
  check suite "MCP tools are unavailable before initialization"
    (beforeReadyReply?.bind errorCode? == some (toJson (-32600 : Int)))

  let (_, versionReply?) ← MCP.handleMessage context MCP.initialSession
    (initializedRequest "2099-01-01")
  check suite "MCP rejects unsupported protocol versions"
    (versionReply?.bind errorCode? == some (toJson (-32602 : Int)))

  let (initialized, initializeReply?) ←
    MCP.handleMessage context MCP.initialSession initializedRequest
  check suite "MCP initialize negotiates the current protocol"
    ((initializeReply?.bind responseResult? >>= fun result =>
      (result.getObjVal? "protocolVersion" >>= Json.getStr?).toOption) ==
      some MCP.protocolVersion && initialized.phase == .initialized)

  let initializedNotification := Json.mkObj [
    ("jsonrpc", toJson "2.0"), ("method", toJson "notifications/initialized")]
  let (ready, notificationReply?) ←
    MCP.handleMessage context initialized initializedNotification
  check suite "MCP initialized notification emits no response"
    (notificationReply?.isNone && ready.phase == .ready)

  let duplicateInitialize := (← MCP.handleMessage context ready initializedRequest).2
  check suite "MCP rejects duplicate initialization"
    (duplicateInitialize.bind errorCode? == some (toJson (-32600 : Int)))

  let listRequest := Json.mkObj [("jsonrpc", toJson "2.0"), ("id", toJson (17 : Nat)),
    ("method", toJson "tools/list"), ("params", Json.mkObj [])]
  let (_, listReply?) ← MCP.handleMessage context ready listRequest
  let listedTools? := listReply? >>= responseResult? >>= fun result =>
    (result.getObjVal? "tools" >>= Json.getArr?).toOption
  check suite "MCP lists every typed Frontier operation once"
    (listedTools?.map (·.size) == some API.operationContracts.size)
  check suite "MCP tool names are unique"
    (API.operationContracts.toList.map (·.operation) |>.Pairwise (· != ·))
  check suite "MCP preserves numeric JSON-RPC ids"
    (listReply?.bind (field? · "id") == some (toJson (17 : Nat)))
  check suite "MCP tool schemas reject additional properties"
    (listedTools?.all fun tools => tools.all fun tool =>
      (field? tool "inputSchema" >>= fun schema =>
        schema.getObjValAs? Bool "additionalProperties" |>.toOption) == some false)

  let unknownNotification := Json.mkObj [
    ("jsonrpc", toJson "2.0"), ("method", toJson "unknown/notification")]
  let (_, unknownNotificationReply?) ← MCP.handleMessage context ready unknownNotification
  check suite "MCP never responds to unknown notifications" unknownNotificationReply?.isNone

  let unknownTool := Json.mkObj [("jsonrpc", toJson "2.0"), ("id", toJson "unknown"),
    ("method", toJson "tools/call"), ("params", Json.mkObj [
      ("name", toJson "missing.tool"), ("arguments", Json.mkObj [])])]
  let (_, unknownToolReply?) ← MCP.handleMessage context ready unknownTool
  check suite "MCP unknown tools are protocol errors"
    (unknownToolReply?.bind errorCode? == some (toJson (-32602 : Int)))

  let invalidSearch := Json.mkObj [("jsonrpc", toJson "2.0"), ("id", toJson "bad-search"),
    ("method", toJson "tools/call"), ("params", Json.mkObj [
      ("name", toJson "declarations.search"), ("arguments", Json.mkObj [])])]
  let (_, invalidSearchReply?) ← MCP.handleMessage context ready invalidSearch
  let invalidSearchError? := invalidSearchReply? >>= responseResult? >>= fun result =>
    result.getObjValAs? Bool "isError" |>.toOption
  check suite "MCP Frontier validation failures are tool execution errors"
    (invalidSearchError? == some true)

  let environmentCall := Json.mkObj [("jsonrpc", toJson "2.0"), ("id", toJson "env"),
    ("method", toJson "tools/call"), ("params", Json.mkObj [
      ("name", toJson "environment.describe"), ("arguments", Json.mkObj [])])]
  let (_, environmentReply?) ← MCP.handleMessage context ready environmentCall
  let structuredOk? := environmentReply? >>= responseResult? >>= fun result =>
    field? result "structuredContent" >>= fun structured =>
      structured.getObjValAs? Bool "ok" |>.toOption
  check suite "MCP successful tools return structured Frontier envelopes"
    (structuredOk? == some true)

  let attemptId := "mcp-test-attempt"
  let attemptPath := context.workRoot / s!"{attemptId}.jsonl"
  if ← attemptPath.pathExists then IO.FS.removeFile attemptPath
  let createAttempt := Json.mkObj [("jsonrpc", toJson "2.0"), ("id", toJson "create"),
    ("method", toJson "tools/call"), ("params", Json.mkObj [
      ("name", toJson "research.attempt.create"),
      ("arguments", Json.mkObj [("attemptId", toJson attemptId),
        ("title", toJson "MCP provenance"), ("goal", toJson "Test the adapter")])])]
  let (_, createReply?) ← MCP.handleMessage context ready createAttempt
  check suite "MCP delegates mutating tools through the typed protocol"
    ((createReply? >>= responseResult? >>= fun result =>
      result.getObjValAs? Bool "isError" |>.toOption) == some false)
  match ← Research.readEvents context.workRoot ⟨attemptId⟩ with
  | .error message => check suite "MCP records client provenance" false message
  | .ok events =>
      check suite "MCP records client provenance"
        (events.all fun event => event.actor.name == "mcp-test-client" &&
          event.actor.runId.value == "mcp-stdio-session")
  if ← attemptPath.pathExists then IO.FS.removeFile attemptPath

  let _ ← readySession context
  pure ()

end Frontier.Test
