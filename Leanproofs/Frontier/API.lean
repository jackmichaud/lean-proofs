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

inductive AttemptRequirement where
  | none
  | required
  | requiredNew
  deriving BEq, DecidableEq, Inhabited, Repr

def AttemptRequirement.toString : AttemptRequirement → String
  | .none => "none"
  | .required => "required"
  | .requiredNew => "required-new"

structure OperationContract where
  operation : String
  description : String
  attempt : AttemptRequirement
  effect : String
  requiredParams : Array String := #[]
  optionalParams : Array String := #[]
  properties : List (String × Json) := []
  extra : List (String × Json) := []

private def stringProperty (description : String) : Json :=
  Json.mkObj [("type", toJson "string"), ("description", toJson description)]

private def positiveIntegerProperty (description : String) : Json :=
  Json.mkObj [("type", toJson "integer"), ("minimum", toJson (1 : Nat)),
    ("description", toJson description)]

private def booleanProperty (description : String) : Json :=
  Json.mkObj [("type", toJson "boolean"), ("description", toJson description)]

private def actionSchema : Json := Json.mkObj [
  ("type", toJson "object"),
  ("additionalProperties", toJson false),
  ("properties", Json.mkObj [
    ("id", stringProperty "Caller-chosen action correlation id."),
    ("tactic", stringProperty "Lean tactic block to evaluate."),
    ("transitionId", stringProperty "Durable id for this proposed transition."),
    ("retrievalIds", Json.mkObj [("type", toJson "array"),
      ("items", Json.mkObj [("type", toJson "string")]),
      ("description", toJson "Premise retrievals used to propose this action.")])]),
  ("required", toJson #["id", "tactic", "transitionId"])]

/-- The operation registry is the source for both native capability discovery and MCP tools. -/
def operationContracts : Array OperationContract := #[
  { operation := "capabilities.get"
    description := "Describe Frontier's typed operations and trust boundary."
    attempt := .none, effect := "read" },
  { operation := "environment.describe"
    description := "Describe the loaded Lean, mathlib, catalog, and policy environment."
    attempt := .none, effect := "read" },
  { operation := "research.attempt.create"
    description := "Create a durable research attempt, optionally opening its Lean proposition."
    attempt := .requiredNew, effect := "append"
    requiredParams := #["title", "goal"]
    optionalParams := #["proposition", "note", "parentAttemptId"]
    properties := [
      ("title", stringProperty "Short title for this research attempt."),
      ("goal", stringProperty "Human-readable research objective."),
      ("proposition", stringProperty "Exact Lean proposition to open as a proof state."),
      ("note", stringProperty "Optional research note."),
      ("parentAttemptId", stringProperty "Attempt from which this work branches.")] },
  { operation := "research.attempt.list"
    description := "List durable research attempts and their materialized state."
    attempt := .none, effect := "read" },
  { operation := "research.attempt.get"
    description := "Read one attempt's summary and complete append-only event history."
    attempt := .required, effect := "read" },
  { operation := "declarations.search"
    description := "Search declarations in the loaded Lean environment by name."
    attempt := .none, effect := "read"
    requiredParams := #["query"]
    optionalParams := #["limit", "includeDefinitions"]
    properties := [
      ("query", stringProperty "Declaration name fragment to search for."),
      ("limit", positiveIntegerProperty "Maximum results to return."),
      ("includeDefinitions", booleanProperty "Include definitions as well as theorems.")] },
  { operation := "premises.retrieve"
    description := "Rank likely Lean premises for a goal and record the retrieval."
    attempt := .required, effect := "append"
    requiredParams := #["goal", "retrievalId"]
    optionalParams := #["limit"]
    properties := [
      ("goal", stringProperty "Lean proposition for which to retrieve premises."),
      ("retrievalId", stringProperty "Durable caller-chosen retrieval id."),
      ("limit", positiveIntegerProperty "Maximum premises to return.")] },
  { operation := "proof.evaluateBatch"
    description := "Evaluate independent Lean tactic candidates from one durable proof state."
    attempt := .required, effect := "append"
    requiredParams := #["parentStateId", "actions"]
    optionalParams := #["heartbeats"]
    properties := [
      ("parentStateId", stringProperty "Durable attempt-scoped parent proof state id."),
      ("actions", Json.mkObj [("type", toJson "array"), ("minItems", toJson (1 : Nat)),
        ("items", actionSchema), ("description", toJson "Independent tactics to evaluate.")]),
      ("heartbeats", positiveIntegerProperty "Lean heartbeat budget per action.")]
    extra := [("actionRequired", toJson #["id", "tactic", "transitionId"]),
      ("actionOptional", toJson #["retrievalIds"])] },
  { operation := "proof.inspectState"
    description := "Inspect a live attempt-scoped Lean proof state."
    attempt := .required, effect := "read"
    requiredParams := #["stateId"]
    optionalParams := #["heartbeats"]
    properties := [
      ("stateId", stringProperty "Durable attempt-scoped proof state id."),
      ("heartbeats", positiveIntegerProperty "Lean heartbeat budget.")] },
  { operation := "proof.rehydrate"
    description := "Replay checked attempt history to restore a durable proof state."
    attempt := .required, effect := "session"
    requiredParams := #["stateId"]
    optionalParams := #["heartbeats"]
    properties := [
      ("stateId", stringProperty "Durable attempt-scoped proof state id."),
      ("heartbeats", positiveIntegerProperty "Lean heartbeat budget for replay.")] }
]

def operationContract? (operation : String) : Option OperationContract :=
  operationContracts.find? (·.operation == operation)

def OperationContract.inputSchema (contract : OperationContract) : Json :=
  let transportProperties :=
    [("environment", stringProperty "Optional loaded-environment fingerprint to require")] ++
    if contract.attempt == .none then [] else
      [("attemptId", stringProperty "Durable research attempt id")]
  let required := if contract.attempt == .none then contract.requiredParams else
    #["attemptId"] ++ contract.requiredParams
  Json.mkObj [
    ("type", toJson "object"),
    ("additionalProperties", toJson false),
    ("properties", Json.mkObj (transportProperties ++ contract.properties)),
    ("required", toJson required)]

private def OperationContract.capabilityJson (contract : OperationContract) : Json :=
  Json.mkObj ([
    ("operation", toJson contract.operation),
    ("attempt", toJson contract.attempt.toString),
    ("effect", toJson contract.effect),
    ("requiredParams", toJson contract.requiredParams),
    ("optionalParams", toJson contract.optionalParams)
  ] ++ contract.extra)

/-- Stable machine-readable failures. New cases may be added without changing existing codes. -/
inductive ErrorCode where
  | invalidRequest
  | invalidParams
  | unsupportedApiVersion
  | unsupportedOperation
  | environmentMismatch
  | invalidGoal
  | stateNotFound
  | replayDiverged
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
  | .replayDiverged => "REPLAY_DIVERGED"
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
  parentStateId : Research.ProofStateId
  actions : Array BatchAction
  heartbeats : Nat := CLI.defaultTacticHeartbeats

structure InspectParams where
  stateId : Research.ProofStateId
  heartbeats : Nat := CLI.defaultTacticHeartbeats

structure RehydrateParams where
  stateId : Research.ProofStateId
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

private def exactOperationParams (operation : String) (json : Json) : Except Error Unit := do
  let some contract := operationContract? operation
    | throw { code := .internalError, message := s!"missing operation contract '{operation}'" }
  exactObject json contract.requiredParams.toList contract.optionalParams.toList

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

private def proofStateId (json : Json) (key : String) : Except Error Research.ProofStateId := do
  let value ← paramString json key
  Research.ProofStateId.parse value |>.mapError fun message =>
    { code := .invalidParams, message }

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

def environmentId (context : CLI.Context) : String :=
  context.fingerprint.identifier

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
    ("operations", toJson (operationContracts.map (·.operation))),
    ("envelope", Json.mkObj [
      ("required", toJson #["apiVersion", "requestId", "operation", "params", "provenance"]),
      ("optional", toJson #["environment", "attemptId"]),
      ("provenanceRequired", toJson #["kind", "name", "runId"]),
      ("provenanceOptional", toJson #["model", "configuration"])]),
    ("contracts", Json.arr (operationContracts.map (·.capabilityJson))),
    ("researchHistory", Json.mkObj [
      ("schemaVersion", toJson (3 : Nat)), ("trusted", toJson false),
      ("appendOnly", toJson true)]),
    ("transport", toJson "local-ndjson"),
    ("authority", toJson "local-process"),
    ("remoteAuthority", toJson false)
  ]

def environmentJson (context : CLI.Context) : Json :=
  let reproducibility := match context.fingerprint.reproducibility with
    | .contentAddressed => (true, #[])
    | .nonContentAddressed reasons => (false, reasons)
  Json.mkObj [
    ("identifier", toJson (environmentId context)),
    ("leanVersion", toJson context.fingerprint.environment.leanVersion),
    ("mathlibRevision", toJson context.fingerprint.environment.mathlibRevision),
    ("frontierRevision", toJson context.fingerprint.environment.frontierRevision),
    ("importsHash", toJson context.fingerprint.environment.importsHash),
    ("policyVersion", toJson context.fingerprint.environment.policyVersion),
    ("catalogEntries", toJson context.catalog.size),
    ("contentAddressed", toJson reproducibility.1),
    ("reproducibilityWarnings", toJson reproducibility.2)
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
  exactOperationParams request.operation request.params

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
  exactOperationParams "research.attempt.create" request.params
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
  exactOperationParams "declarations.search" request.params
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
  exactOperationParams "premises.retrieve" request.params
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
  exactOperationParams "proof.evaluateBatch" request.params
  let parentStateId ← proofStateId request.params "parentStateId"
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
  exactOperationParams "proof.inspectState" request.params
  let stateId ← proofStateId request.params "stateId"
  let heartbeats ← optionalNat request.params "heartbeats" CLI.defaultTacticHeartbeats
  if heartbeats == 0 then fail .invalidParams "field 'heartbeats' must be positive in a session"
  return { stateId, heartbeats }

def rehydrateParams (request : Request) : Except Error RehydrateParams := do
  exactOperationParams "proof.rehydrate" request.params
  let stateId ← proofStateId request.params "stateId"
  let heartbeats ← optionalNat request.params "heartbeats" CLI.defaultTacticHeartbeats
  if heartbeats == 0 then fail .invalidParams "field 'heartbeats' must be positive in a session"
  return { stateId, heartbeats }

end Frontier.API
