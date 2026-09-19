/-
Copyright (c) 2026 Jack Michaud. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Michaud
-/

import Leanproofs.Frontier.Protocol

/-!
# Frontier MCP adapter

A newline-delimited JSON-RPC 2.0 adapter for MCP 2025-11-25. Tool execution delegates to the
typed Frontier protocol; this module owns only MCP lifecycle, framing, and envelope translation.
-/

open Lean

namespace Frontier.MCP

def protocolVersion : String := "2025-11-25"

inductive Phase where
  | cold
  | initialized
  | ready
  deriving BEq, Inhabited

structure Session where
  phase : Phase := .cold
  clientName : String := "mcp-client"
  clientVersion : String := "unknown"
  deriving Inhabited

def initialSession : Session := {}

private def errorObject (code : Int) (message : String) (data? : Option Json := none) : Json :=
  Json.mkObj ([
    ("code", toJson code),
    ("message", toJson message)
  ] ++ (data?.map fun data => [("data", data)]).getD [])

private def response (id : Json) (result : Json) : Json := Json.mkObj [
  ("jsonrpc", toJson "2.0"), ("id", id), ("result", result)]

private def errorResponse (id : Json := .null) (code : Int) (message : String)
    (data? : Option Json := none) : Json := Json.mkObj [
  ("jsonrpc", toJson "2.0"), ("id", id), ("error", errorObject code message data?)]

private def field? (json : Json) (key : String) : Option Json :=
  json.getObjVal? key |>.toOption

private def stringField? (json : Json) (key : String) : Option String :=
  field? json key >>= fun value => value.getStr?.toOption

private def validId : Json → Bool
  | .str _ | .num _ => true
  | _ => false

private def objectParams? (json : Json) : Option Json :=
  match field? json "params" with
  | none => some (Json.mkObj [])
  | some value => value.getObj?.toOption.map fun _ => value

private def toolJson (contract : API.OperationContract) : Json := Json.mkObj [
  ("name", toJson contract.operation),
  ("description", toJson contract.description),
  ("inputSchema", contract.inputSchema),
  ("annotations", Json.mkObj [
    ("readOnlyHint", toJson (contract.effect == "read")),
    ("destructiveHint", toJson false),
    ("idempotentHint", toJson (contract.effect == "read")),
    ("openWorldHint", toJson false)])]

def toolsJson : Json :=
  Json.mkObj [("tools", Json.arr (API.operationContracts.map toolJson))]

private def handleInitialize (session : Session) (id params : Json) : Session × Json :=
  if session.phase != .cold then
    (session, errorResponse id (-32600) "initialize may only be sent once")
  else
    let version? := stringField? params "protocolVersion"
    let clientInfo? := field? params "clientInfo"
    let capabilitiesOk := (field? params "capabilities").any (fun value => value.getObj?.isOk)
    match version?, clientInfo? with
    | some version, some clientInfo =>
        let clientName? := stringField? clientInfo "name"
        let clientVersion? := stringField? clientInfo "version"
        if !capabilitiesOk || clientName?.isNone || clientVersion?.isNone ||
            clientName?.any (·.trimAscii.isEmpty) || clientVersion?.any (·.trimAscii.isEmpty) then
          (session, errorResponse id (-32602) "initialize requires object capabilities and clientInfo name/version")
        else if version != protocolVersion then
          (session, errorResponse id (-32602) "unsupported MCP protocol version"
            (some (Json.mkObj [("requested", toJson version),
              ("supported", toJson #[protocolVersion])])))
        else
          let next : Session := {
            phase := .initialized
            clientName := clientName?.get!
            clientVersion := clientVersion?.get!
          }
          (next, response id (Json.mkObj [
            ("protocolVersion", toJson protocolVersion),
            ("capabilities", Json.mkObj [("tools", Json.mkObj [("listChanged", toJson false)])]),
            ("serverInfo", Json.mkObj [
              ("name", toJson "frontier"),
              ("title", toJson "Frontier Lean Research Registry"),
              ("version", toJson "0.1.0")]),
            ("instructions", toJson "Use durable research attempts for proof work. Lean verification and the axiom policy, not tool output, determine truth.")]))
    | _, _ =>
        (session, errorResponse id (-32602)
          "initialize requires protocolVersion, capabilities, and clientInfo")

private def frontierRequest (session : Session) (id : Json) (contract : API.OperationContract)
    (arguments : Json) : Except String API.Request := do
  let fields ← arguments.getObj? |>.mapError fun _ => "tool arguments must be an object"
  if contract.attempt == .none && (field? arguments "attemptId").isSome then
    throw s!"tool '{contract.operation}' does not accept field 'attemptId'"
  let environment? ← match field? arguments "environment" with
    | none => pure none
    | some value => some <$> value.getStr?.mapError fun _ => "field 'environment' must be a string"
  let attemptId? ← match field? arguments "attemptId" with
    | none => pure none
    | some value =>
        let text ← value.getStr?.mapError fun _ => "field 'attemptId' must be a string"
        some <$> Research.AttemptId.parse text
  let params := Json.mkObj <| fields.toList.filter fun pair =>
    pair.1 != "environment" && pair.1 != "attemptId"
  return {
    apiVersion := API.version
    requestId := id.compress
    operation := contract.operation
    environment?
    attemptId?
    params
    actor := {
      kind := .agent
      name := session.clientName
      runId := ⟨"mcp-stdio-session"⟩
      configuration? := some s!"MCP {protocolVersion}; client {session.clientVersion}"
    }
  }

private def toolResult (frontier : Json) : Json :=
  let ok := (frontier.getObjValAs? Bool "ok").toOption.getD false
  Json.mkObj [
    ("content", Json.arr #[Json.mkObj [
      ("type", toJson "text"), ("text", toJson frontier.compress)]]),
    ("structuredContent", frontier),
    ("isError", toJson (!ok))]

private def callTool (context : CLI.Context) (session : Session) (id params : Json) : IO Json := do
  let some name := stringField? params "name"
    | return errorResponse id (-32602) "tools/call requires string field 'name'"
  let some contract := API.operationContract? name
    | return errorResponse id (-32602) s!"unknown tool '{name}'"
  let arguments := field? params "arguments" |>.getD (Json.mkObj [])
  unless arguments.getObj?.isOk do
    return errorResponse id (-32602) "tools/call field 'arguments' must be an object"
  let request ← match frontierRequest session id contract arguments with
    | .ok value => pure value
    | .error message => return response id (toolResult (API.failureResponse context
        (some id.compress) (some name) { code := .invalidParams, message }))
  try
    return response id (toolResult (← CLI.computeTyped context request))
  catch exception =>
    IO.eprintln s!"MCP tool '{name}' failed: {exception}"
    return errorResponse id (-32603) "Frontier tool execution failed"

/-- Handle one parsed MCP message. `none` means the input was a notification. -/
def handleMessage (context : CLI.Context) (session : Session) (json : Json) :
    IO (Session × Option Json) := do
  let fields ← match json.getObj? with
    | .ok value => pure value
    | .error _ => return (session, some (errorResponse .null (-32600) "invalid JSON-RPC request"))
  let id? := fields["id"]?
  if id?.any (fun id => !validId id) then
    return (session, some (errorResponse .null (-32600) "request id must be a string or number"))
  let isNotification := id?.isNone
  let fail (code : Int) (message : String) : Session × Option Json :=
    if isNotification then (session, none)
    else (session, some (errorResponse id?.get! code message))
  unless stringField? json "jsonrpc" == some "2.0" do
    return fail (-32600) "jsonrpc must be '2.0'"
  let some method := stringField? json "method"
    | return fail (-32600) "method must be a string"
  let some params := objectParams? json
    | return fail (-32602) "params must be an object when present"
  match method with
  | "initialize" =>
      if isNotification then return (session, none)
      let (next, reply) := handleInitialize session id?.get! params
      return (next, some reply)
  | "notifications/initialized" =>
      if !isNotification then return fail (-32600) "notifications/initialized must not have an id"
      if session.phase == .initialized then return ({ session with phase := .ready }, none)
      return (session, none)
  | "ping" =>
      if isNotification then return (session, none)
      return (session, some (response id?.get! (Json.mkObj [])))
  | "tools/list" =>
      if session.phase != .ready then return fail (-32600) "MCP session is not initialized"
      if (field? params "cursor").isSome then return fail (-32602) "Frontier tools are not paginated"
      if isNotification then return (session, none)
      return (session, some (response id?.get! toolsJson))
  | "tools/call" =>
      if session.phase != .ready then return fail (-32600) "MCP session is not initialized"
      if isNotification then return (session, none)
      return (session, some (← callTool context session id?.get! params))
  | _ => return fail (-32601) s!"method not found: {method}"

def handleLine (context : CLI.Context) (session : Session) (source : String) :
    IO (Session × Option Json) :=
  match Json.parse source with
  | .error _ => pure (session, some (errorResponse .null (-32700) "parse error"))
  | .ok json => handleMessage context session json

partial def loop (context : CLI.Context) (session : Session)
    (stdin stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return ()
  let (next, reply?) ← handleLine context session line.trimAscii.toString
  if let some reply := reply? then
    stdout.putStr (reply.compress ++ "\n")
    stdout.flush
  loop context next stdin stdout

def run (context : CLI.Context) : IO UInt32 := do
  loop { context with session := true } initialSession (← IO.getStdin) (← IO.getStdout)
  return 0

end Frontier.MCP
