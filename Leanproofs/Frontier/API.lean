/-
Copyright (c) 2026 Jack Michaud. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Michaud
-/

import Leanproofs.Frontier.Command

/-!
# Frontier agent API

A typed, versioned envelope for local agents. This is a protocol model, not a network or
authority boundary: `frontier serve` remains a local process and typed requests have exactly
the same authority as the legacy argument-array protocol.
-/

open Lean

namespace Frontier.API

def version : String := "frontier.agent/v1"

/-- Stable machine-readable failures. New cases may be added without changing existing codes. -/
inductive ErrorCode where
  | invalidRequest
  | unsupportedApiVersion
  | unsupportedOperation
  | environmentMismatch
  | commandFailed
  | internalError
  deriving BEq, DecidableEq, Inhabited, Repr

def ErrorCode.toString : ErrorCode → String
  | .invalidRequest => "INVALID_REQUEST"
  | .unsupportedApiVersion => "UNSUPPORTED_API_VERSION"
  | .unsupportedOperation => "UNSUPPORTED_OPERATION"
  | .environmentMismatch => "ENVIRONMENT_MISMATCH"
  | .commandFailed => "COMMAND_FAILED"
  | .internalError => "INTERNAL_ERROR"

structure Error where
  code : ErrorCode
  message : String
  deriving Inhabited, Repr

/-- One structured request. `params` and `provenance` are retained as JSON objects so the
envelope can evolve without turning transport concerns into Lean command-line types. -/
structure Request where
  apiVersion : String
  requestId : String
  operation : String
  environment? : Option String
  params : Json
  provenance : Json
  deriving Inhabited

private def requiredString (json : Json) (key : String) : Except Error String := do
  let value ← json.getObjVal? key |>.mapError fun _ =>
    { code := .invalidRequest, message := s!"missing required string field '{key}'" }
  let text ← value.getStr? |>.mapError fun _ =>
    { code := .invalidRequest, message := s!"field '{key}' must be a string" }
  if text.isEmpty then
    throw { code := .invalidRequest, message := s!"field '{key}' must not be empty" }
  return text

private def optionalString (json : Json) (key : String) : Except Error (Option String) :=
  match json.getObjVal? key with
  | .error _ => .ok none
  | .ok .null => .ok none
  | .ok value =>
      match value.getStr? with
      | .error _ => .error {
          code := .invalidRequest
          message := s!"field '{key}' must be a string or null"
        }
      | .ok text =>
          if text.isEmpty then
            .error { code := .invalidRequest, message := s!"field '{key}' must not be empty" }
          else
            .ok (some text)

private def requiredObject (json : Json) (key : String) : Except Error Json := do
  let value ← json.getObjVal? key |>.mapError fun _ =>
    { code := .invalidRequest, message := s!"missing required object field '{key}'" }
  let _ ← value.getObj? |>.mapError fun _ =>
    { code := .invalidRequest, message := s!"field '{key}' must be an object" }
  return value

/-- Decode a typed request object. Legacy arrays are intentionally decoded by `Protocol` so
their accepted syntax and error responses remain byte-for-byte compatible. -/
def requestOfJson (json : Json) : Except Error Request := do
  let _ ← json.getObj? |>.mapError fun _ =>
    { code := .invalidRequest, message := "a typed request must be a JSON object" }
  return {
    apiVersion := ← requiredString json "apiVersion"
    requestId := ← requiredString json "requestId"
    operation := ← requiredString json "operation"
    environment? := ← optionalString json "environment"
    params := ← requiredObject json "params"
    provenance := ← requiredObject json "provenance"
  }

def parseRequest (source : String) : Except Error Request := do
  let json ← Json.parse source |>.mapError fun message =>
    { code := .invalidRequest, message := s!"invalid JSON request: {message}" }
  requestOfJson json

/-- Recover correlation fields from an invalid envelope when possible. A structural error in
`params` should not force an agent to guess which concurrent request failed. -/
def requestMetadata (source : String) : Option String × Option String :=
  match Json.parse source with
  | .error _ => (none, none)
  | .ok json =>
      let field? (key : String) : Option String :=
        (json.getObjVal? key >>= Json.getStr?).toOption
      (field? "requestId", field? "operation")

/-- Identifies the loaded logical environment for request pinning. The catalog signature is a
local compatibility identifier, not a cryptographic snapshot fingerprint; a future snapshot
service can replace it in the next API version. -/
def environmentId (context : CLI.Context) : String :=
  let signature := "|".intercalate <| context.catalog.toList.map fun entry =>
    s!"{entry.id}:{entry.statement}:{entry.certificate?.map Name.toString |>.getD "-"}"
  s!"frontier-local:lean-{Lean.versionString}:catalog-{hash signature}"

def errorJson (error : Error) : Json :=
  Json.mkObj [
    ("code", toJson error.code.toString),
    ("message", toJson error.message)
  ]

private def optionStringJson : Option String → Json
  | some value => toJson value
  | none => .null

def responseJson (requestId? operation? : Option String) (environment : String)
    (result? : Option Json) (error? : Option Error) : Json :=
  Json.mkObj [
    ("apiVersion", toJson version),
    ("requestId", optionStringJson requestId?),
    ("operation", optionStringJson operation?),
    ("ok", toJson error?.isNone),
    ("environment", toJson environment),
    ("result", result?.getD .null),
    ("error", match error? with | some error => errorJson error | none => .null)
  ]

def successResponse (context : CLI.Context) (request : Request) (result : Json) : Json :=
  responseJson (some request.requestId) (some request.operation) (environmentId context)
    (some result) none

def failureResponse (context : CLI.Context) (requestId? operation? : Option String)
    (error : Error) : Json :=
  responseJson requestId? operation? (environmentId context) none (some error)

def capabilitiesJson : Json :=
  Json.mkObj [
    ("apiVersions", toJson #[version]),
    ("operations", toJson #["capabilities.get", "environment.describe", "cli.execute"]),
    ("legacyArrayProtocol", toJson true),
    ("transport", toJson "local-ndjson"),
    ("authority", toJson "local-process")
  ]

def environmentJson (context : CLI.Context) : Json :=
  Json.mkObj [
    ("identifier", toJson (environmentId context)),
    ("leanVersion", toJson Lean.versionString),
    ("catalogEntries", toJson context.catalog.size),
    ("contentAddressed", toJson false)
  ]

def validateRequest (context : CLI.Context) (request : Request) : Except Error Unit := do
  unless request.apiVersion == version do
    throw {
      code := .unsupportedApiVersion
      message := s!"unsupported API version '{request.apiVersion}'; expected '{version}'"
    }
  if let some requested := request.environment? then
    let loaded := environmentId context
    unless requested == loaded do
      throw {
        code := .environmentMismatch
        message := s!"request targets environment '{requested}', but '{loaded}' is loaded"
      }

/-- Read the explicit compatibility operation's argument array. No other operation can reach
the legacy dispatcher through this function. -/
def cliArgs (request : Request) : Except Error (List String) := do
  let value ← request.params.getObjVal? "args" |>.mapError fun _ => {
    code := .invalidRequest
    message := "operation 'cli.execute' requires params.args"
  }
  let values ← value.getArr? |>.mapError fun _ => {
    code := .invalidRequest
    message := "field 'params.args' must be an array of strings"
  }
  let args ← values.mapM fun value =>
    value.getStr? |>.mapError fun _ => {
      code := .invalidRequest
      message := "field 'params.args' must be an array of strings"
    }
  return args.toList

end Frontier.API
