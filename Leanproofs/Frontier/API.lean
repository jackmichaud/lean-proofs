/-
Copyright (c) 2026 Jack Michaud. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Michaud
-/

import Leanproofs.Frontier.Command

/-!
# Frontier agent API

The only protocol accepted by `frontier serve`. This is a local process protocol, not a
network or remote authority boundary.
-/

open Lean

namespace Frontier.API

def version : String := "frontier.agent/v1"

/-- Stable machine-readable failures. New cases may be added without changing existing codes. -/
inductive ErrorCode where
  | invalidRequest
  | invalidParams
  | unsupportedApiVersion
  | unsupportedOperation
  | environmentMismatch
  | invalidGoal
  | stateNotFound
  | researchState
  | internalError
  deriving BEq, DecidableEq, Inhabited, Repr

def ErrorCode.toString : ErrorCode → String
  | .invalidRequest => "INVALID_REQUEST"
  | .invalidParams => "INVALID_PARAMS"
  | .unsupportedApiVersion => "UNSUPPORTED_API_VERSION"
  | .unsupportedOperation => "UNSUPPORTED_OPERATION"
  | .environmentMismatch => "ENVIRONMENT_MISMATCH"
  | .invalidGoal => "INVALID_GOAL"
  | .stateNotFound => "STATE_NOT_FOUND"
  | .researchState => "RESEARCH_STATE_ERROR"
  | .internalError => "INTERNAL_ERROR"

structure Error where
  code : ErrorCode
  message : String
  deriving Inhabited, Repr

/-- One structured request. Research operations name their attempt in the envelope; all
requests carry typed actor provenance, even when an operation does not append an event. -/
structure Request where
  apiVersion : String
  requestId : String
  operation : String
  environment? : Option String
  attemptId? : Option Research.AttemptId
  params : Json
  actor : Research.Actor
  deriving Inhabited

structure AttemptCreateParams where
  title : String
  goal : String
  proposition? : Option String := none
  note? : Option String := none
  parentAttemptId? : Option Research.AttemptId := none

structure SearchParams where
  query : String
  limit : Nat := CLI.defaultSearchLimit
  includeDefinitions : Bool := false

structure PremiseParams where
  goal : String
  retrievalId : Research.RetrievalId
  limit : Nat := CLI.defaultSuggestLimit

structure BatchAction where
  id : String
  tactic : String
  transitionId : Research.TransitionId
  retrievalIds : Array Research.RetrievalId := #[]

structure BatchParams where
  parentStateId : Nat
  actions : Array BatchAction
  heartbeats : Nat := CLI.defaultTacticHeartbeats

structure InspectParams where
  stateId : Nat
  heartbeats : Nat := CLI.defaultTacticHeartbeats

private def fail (code : ErrorCode) (message : String) : Except Error α :=
  .error { code, message }

private def exactObject (json : Json) (required optional : List String)
    (code : ErrorCode := .invalidParams) : Except Error Unit := do
  let fields ← json.getObj? |>.mapError fun _ => { code, message := "expected a JSON object" }
  let actual := fields.foldl (init := []) fun keys key _ => key :: keys
  let allowed := required ++ optional
  let unexpected := actual.filter fun key => !allowed.contains key
  let missing := required.filter fun key => !actual.contains key
  unless unexpected.isEmpty do
    throw { code, message := s!"unexpected field(s): {", ".intercalate unexpected}" }
  unless missing.isEmpty do
    throw { code, message := s!"missing field(s): {", ".intercalate missing}" }

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

private def actorKind (value : String) : Except Error Research.ActorKind :=
  match value with
  | "human" => .ok .human
  | "agent" => .ok .agent
  | "tool" => .ok .tool
  | "system" => .ok .system
  | _ => fail .invalidRequest
      "provenance field 'kind' must be human, agent, tool, or system"

private def actorOfJson (json : Json) : Except Error Research.Actor := do
  exactObject json ["kind", "name", "runId"] ["model", "configuration"] .invalidRequest
  let runIdText ← requiredString json "runId"
  let runId ← Research.RunId.parse runIdText |>.mapError fun message =>
    { code := .invalidRequest, message }
  return {
    kind := ← actorKind (← requiredString json "kind")
    name := ← requiredString json "name"
    runId
    model? := ← optionalString json "model"
    configuration? := ← optionalString json "configuration"
  }

private def paramField (json : Json) (key : String) : Except Error Json :=
  json.getObjVal? key |>.mapError fun _ =>
    { code := .invalidParams, message := s!"missing required field '{key}'" }

private def paramString (json : Json) (key : String) : Except Error String := do
  let value ← (← paramField json key).getStr? |>.mapError fun _ =>
    { code := .invalidParams, message := s!"field '{key}' must be a string" }
  if value.isEmpty then fail .invalidParams s!"field '{key}' must not be empty"
  return value

private def paramNat (json : Json) (key : String) : Except Error Nat := do
  (← paramField json key).getNat? |>.mapError fun _ =>
    { code := .invalidParams, message := s!"field '{key}' must be a non-negative integer" }

private def optionalNat (json : Json) (key : String) (fallback : Nat) : Except Error Nat :=
  match json.getObjVal? key with
  | .error _ => .ok fallback
  | .ok value => value.getNat? |>.mapError fun _ =>
      { code := .invalidParams, message := s!"field '{key}' must be a non-negative integer" }

private def optionalBool (json : Json) (key : String) (fallback : Bool) : Except Error Bool :=
  match json.getObjVal? key with
  | .error _ => .ok fallback
  | .ok value => value.getBool? |>.mapError fun _ =>
      { code := .invalidParams, message := s!"field '{key}' must be a boolean" }

/-- Decode the exact typed request envelope. Arrays and unknown envelope fields are rejected. -/
def requestOfJson (json : Json) : Except Error Request := do
  exactObject json ["apiVersion", "requestId", "operation", "params", "provenance"]
    ["environment", "attemptId"] .invalidRequest
  let attemptId? ← match ← optionalString json "attemptId" with
    | none => pure none
    | some value => some <$> (Research.AttemptId.parse value |>.mapError fun message =>
        { code := .invalidRequest, message })
  return {
    apiVersion := ← requiredString json "apiVersion"
    requestId := ← requiredString json "requestId"
    operation := ← requiredString json "operation"
    environment? := ← optionalString json "environment"
    attemptId?
    params := ← requiredObject json "params"
    actor := ← actorOfJson (← requiredObject json "provenance")
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
    ("operations", toJson #["capabilities.get", "environment.describe",
      "research.attempt.create", "declarations.search", "premises.retrieve", "proof.evaluateBatch",
      "proof.inspectState"]),
    ("envelope", Json.mkObj [
      ("required", toJson #["apiVersion", "requestId", "operation", "params", "provenance"]),
      ("optional", toJson #["environment", "attemptId"]),
      ("provenanceRequired", toJson #["kind", "name", "runId"]),
      ("provenanceOptional", toJson #["model", "configuration"])]),
    ("contracts", Json.arr #[
      Json.mkObj [("operation", toJson "capabilities.get"), ("attempt", toJson "none"),
        ("effect", toJson "read"), ("requiredParams", toJson (#[] : Array String)),
        ("optionalParams", toJson (#[] : Array String))],
      Json.mkObj [("operation", toJson "environment.describe"), ("attempt", toJson "none"),
        ("effect", toJson "read"), ("requiredParams", toJson (#[] : Array String)),
        ("optionalParams", toJson (#[] : Array String))],
      Json.mkObj [("operation", toJson "research.attempt.create"),
        ("attempt", toJson "required-new"), ("effect", toJson "append"),
        ("requiredParams", toJson #["title", "goal"]),
        ("optionalParams", toJson #["proposition", "note", "parentAttemptId"])],
      Json.mkObj [("operation", toJson "declarations.search"), ("attempt", toJson "none"),
        ("effect", toJson "read"), ("requiredParams", toJson #["query"]),
        ("optionalParams", toJson #["limit", "includeDefinitions"])],
      Json.mkObj [("operation", toJson "premises.retrieve"), ("attempt", toJson "required"),
        ("effect", toJson "append"), ("requiredParams", toJson #["goal", "retrievalId"]),
        ("optionalParams", toJson #["limit"])],
      Json.mkObj [("operation", toJson "proof.evaluateBatch"), ("attempt", toJson "required"),
        ("effect", toJson "append"),
        ("requiredParams", toJson #["parentStateId", "actions"]),
        ("optionalParams", toJson #["heartbeats"]),
        ("actionRequired", toJson #["id", "tactic", "transitionId"]),
        ("actionOptional", toJson #["retrievalIds"])],
      Json.mkObj [("operation", toJson "proof.inspectState"), ("attempt", toJson "required"),
        ("effect", toJson "read"), ("requiredParams", toJson #["stateId"]),
        ("optionalParams", toJson #["heartbeats"])]
    ]),
    ("researchHistory", Json.mkObj [
      ("schemaVersion", toJson (2 : Nat)), ("trusted", toJson false),
      ("appendOnly", toJson true)]),
    ("transport", toJson "local-ndjson"),
    ("authority", toJson "local-process"),
    ("remoteAuthority", toJson false)
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

def emptyParams (request : Request) : Except Error Unit :=
  exactObject request.params [] []

def requireAttemptId (request : Request) : Except Error Research.AttemptId :=
  match request.attemptId? with
  | some value =>
      if Journal.isValidId value.value then .ok value
      else fail .invalidParams
        "field 'attemptId' must contain lowercase ASCII letters, digits, and hyphens"
  | none => fail .invalidParams s!"operation '{request.operation}' requires envelope field 'attemptId'"

private def optionalParamString (json : Json) (key : String) : Except Error (Option String) :=
  match json.getObjVal? key with
  | .error _ => .ok none
  | .ok .null => .ok none
  | .ok value =>
      match value.getStr? with
      | .error _ => fail .invalidParams s!"field '{key}' must be a string or null"
      | .ok text =>
          if text.trimAscii.isEmpty then fail .invalidParams s!"field '{key}' must not be blank"
          else .ok (some text)

def attemptCreateParams (request : Request) : Except Error AttemptCreateParams := do
  exactObject request.params ["title", "goal"] ["proposition", "note", "parentAttemptId"]
  let title ← paramString request.params "title"
  let goal ← paramString request.params "goal"
  if title.trimAscii.isEmpty then fail .invalidParams "field 'title' must not be blank"
  if goal.trimAscii.isEmpty then fail .invalidParams "field 'goal' must not be blank"
  let parentAttemptId? ← match ← optionalParamString request.params "parentAttemptId" with
    | none => pure none
    | some value => some <$> (Research.AttemptId.parse value |>.mapError fun message =>
        { code := .invalidParams, message })
  return {
    title := title.trimAscii.toString
    goal := goal.trimAscii.toString
    proposition? := ← optionalParamString request.params "proposition"
    note? := ← optionalParamString request.params "note"
    parentAttemptId?
  }

def searchParams (request : Request) : Except Error SearchParams := do
  exactObject request.params ["query"] ["limit", "includeDefinitions"]
  let query ← paramString request.params "query"
  if query.trimAscii.isEmpty then fail .invalidParams "field 'query' must not be blank"
  let limit ← optionalNat request.params "limit" CLI.defaultSearchLimit
  if limit == 0 then fail .invalidParams "field 'limit' must be positive"
  return {
    query
    limit
    includeDefinitions := ← optionalBool request.params "includeDefinitions" false
  }

def premiseParams (request : Request) : Except Error PremiseParams := do
  exactObject request.params ["goal", "retrievalId"] ["limit"]
  let goal ← paramString request.params "goal"
  if goal.trimAscii.isEmpty then fail .invalidParams "field 'goal' must not be blank"
  let limit ← optionalNat request.params "limit" CLI.defaultSuggestLimit
  if limit == 0 then fail .invalidParams "field 'limit' must be positive"
  let retrievalIdText ← paramString request.params "retrievalId"
  let retrievalId ← Research.RetrievalId.parse retrievalIdText |>.mapError fun message =>
    { code := .invalidParams, message }
  return { goal, retrievalId, limit }

private def batchAction (json : Json) : Except Error BatchAction := do
  exactObject json ["id", "tactic", "transitionId"] ["retrievalIds"]
  let id ← paramString json "id"
  let tactic ← paramString json "tactic"
  if tactic.trimAscii.isEmpty then fail .invalidParams "field 'tactic' must not be blank"
  let transitionIdText ← paramString json "transitionId"
  let transitionId ← Research.TransitionId.parse transitionIdText |>.mapError fun message =>
    { code := .invalidParams, message }
  let retrievalIds ← match json.getObjVal? "retrievalIds" with
    | .error _ => pure #[]
    | .ok value =>
        let values ← value.getArr? |>.mapError fun _ =>
          { code := .invalidParams, message := "field 'retrievalIds' must be an array" }
        values.mapM fun value => do
          let text ← value.getStr? |>.mapError fun _ =>
            { code := .invalidParams, message := "retrieval ids must be strings" }
          Research.RetrievalId.parse text |>.mapError fun message =>
            { code := .invalidParams, message }
  return { id, tactic, transitionId, retrievalIds }

def batchParams (request : Request) : Except Error BatchParams := do
  exactObject request.params ["parentStateId", "actions"] ["heartbeats"]
  let parentStateId ← paramNat request.params "parentStateId"
  let values ← (← paramField request.params "actions").getArr? |>.mapError fun _ =>
    { code := .invalidParams, message := "field 'actions' must be an array" }
  if values.isEmpty then fail .invalidParams "field 'actions' must not be empty"
  let actions ← values.mapM batchAction
  let ids := actions.map (·.id)
  unless ids.toList.Pairwise (· != ·) do
    fail .invalidParams "action ids must be unique within a batch"
  let transitionIds := actions.map (·.transitionId)
  unless transitionIds.toList.Pairwise (· != ·) do
    fail .invalidParams "transition ids must be unique within a batch"
  let heartbeats ← optionalNat request.params "heartbeats" CLI.defaultTacticHeartbeats
  if heartbeats == 0 then fail .invalidParams "field 'heartbeats' must be positive in a session"
  return { parentStateId, actions, heartbeats }

def inspectParams (request : Request) : Except Error InspectParams := do
  exactObject request.params ["stateId"] ["heartbeats"]
  let stateId ← paramNat request.params "stateId"
  let heartbeats ← optionalNat request.params "heartbeats" CLI.defaultTacticHeartbeats
  if heartbeats == 0 then fail .invalidParams "field 'heartbeats' must be positive in a session"
  return { stateId, heartbeats }

end Frontier.API
