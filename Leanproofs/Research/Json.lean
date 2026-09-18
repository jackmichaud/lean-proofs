/-
Copyright (c) 2026 Jack Michaud. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Michaud
-/

import Leanproofs.Research.Model

namespace Frontier.Research

open Lean

private def objectFields (json : Json) : Except String (Std.TreeMap.Raw String Json compare) :=
  json.getObj?

private def exactObject (json : Json) (expected : List String) : Except String Unit := do
  let fields ← objectFields json
  let actual := fields.foldl (init := []) fun keys key _ => key :: keys
  let unexpected := actual.filter fun key => !expected.contains key
  let missing := expected.filter fun key => !actual.contains key
  unless unexpected.isEmpty do
    throw s!"unexpected field(s): {", ".intercalate unexpected}"
  unless missing.isEmpty do
    throw s!"missing field(s): {", ".intercalate missing}"

private def field (json : Json) (key : String) : Except String Json :=
  match json.getObjVal? key with
  | .ok value => .ok value
  | .error _ => .error s!"missing required field '{key}'"

private def stringField (json : Json) (key : String) : Except String String := do
  match (← field json key).getStr? with
  | .ok value => return value
  | .error _ => throw s!"field '{key}' must be a string"

private def natField (json : Json) (key : String) : Except String Nat := do
  match (← field json key).getNat? with
  | .ok value => return value
  | .error _ => throw s!"field '{key}' must be a non-negative integer"

private def boolField (json : Json) (key : String) : Except String Bool := do
  match (← field json key).getBool? with
  | .ok value => return value
  | .error _ => throw s!"field '{key}' must be a boolean"

private def optionalStringField (json : Json) (key : String) : Except String (Option String) := do
  match ← field json key with
  | .null => return none
  | value =>
      match value.getStr? with
      | .ok text => return some text
      | .error _ => throw s!"field '{key}' must be a string or null"

private def optionalNatField (json : Json) (key : String) : Except String (Option Nat) := do
  match ← field json key with
  | .null => return none
  | value =>
      match value.getNat? with
      | .ok number => return some number
      | .error _ => throw s!"field '{key}' must be a non-negative integer or null"

private def stringArrayField (json : Json) (key : String) : Except String (Array String) := do
  let value ← field json key
  let values ← match value.getArr? with
    | .ok values => pure values
    | .error _ => throw s!"field '{key}' must be an array"
  values.mapM fun element =>
    match element.getStr? with
    | .ok text => pure text
    | .error _ => throw s!"field '{key}' must contain only strings"

private def optionJson [ToJson α] : Option α → Json
  | none => .null
  | some value => toJson value

private def idJson (value : String) : Json := toJson value

instance : ToJson AttemptId := ⟨fun id => idJson id.value⟩
instance : ToJson ProofStateId := ⟨fun id => idJson id.value⟩
instance : ToJson TransitionId := ⟨fun id => idJson id.value⟩
instance : ToJson RetrievalId := ⟨fun id => idJson id.value⟩
instance : ToJson RunId := ⟨fun id => idJson id.value⟩
instance : ToJson EventId := ⟨fun id => idJson id.value⟩

private def parseId (kind : String) (parse : String → Except String α) (json : Json) : Except String α := do
  let value ← match json.getStr? with
    | .ok value => pure value
    | .error _ => throw s!"{kind} must be a string"
  parse value

instance : FromJson AttemptId := ⟨parseId "attempt id" AttemptId.parse⟩
instance : FromJson ProofStateId := ⟨parseId "proof state id" ProofStateId.parse⟩
instance : FromJson TransitionId := ⟨parseId "transition id" TransitionId.parse⟩
instance : FromJson RetrievalId := ⟨parseId "retrieval id" RetrievalId.parse⟩
instance : FromJson RunId := ⟨parseId "run id" RunId.parse⟩
instance : FromJson EventId := ⟨parseId "event id" EventId.parse⟩

def environmentJson (value : EnvironmentFingerprint) : Json := Json.mkObj [
  ("leanVersion", toJson value.leanVersion),
  ("mathlibRevision", toJson value.mathlibRevision),
  ("frontierRevision", toJson value.frontierRevision),
  ("importsHash", toJson value.importsHash),
  ("policyVersion", toJson value.policyVersion)
]

def environmentOfJson (json : Json) : Except String EnvironmentFingerprint := do
  exactObject json ["leanVersion", "mathlibRevision", "frontierRevision", "importsHash", "policyVersion"]
  return {
    leanVersion := ← stringField json "leanVersion"
    mathlibRevision := ← stringField json "mathlibRevision"
    frontierRevision := ← stringField json "frontierRevision"
    importsHash := ← stringField json "importsHash"
    policyVersion := ← stringField json "policyVersion"
  }

def ActorKind.toString : ActorKind → String
  | .human => "human" | .agent => "agent" | .tool => "tool" | .system => "system"

def ActorKind.ofString (value : String) : Except String ActorKind :=
  match value with
  | "human" => .ok .human | "agent" => .ok .agent | "tool" => .ok .tool
  | "system" => .ok .system | _ => .error s!"unknown actor kind '{value}'"

def actorJson (value : Actor) : Json := Json.mkObj [
  ("kind", toJson value.kind.toString), ("name", toJson value.name),
  ("runId", toJson value.runId), ("model", optionJson value.model?),
  ("configuration", optionJson value.configuration?)
]

def actorOfJson (json : Json) : Except String Actor := do
  exactObject json ["kind", "name", "runId", "model", "configuration"]
  return {
    kind := ← ActorKind.ofString (← stringField json "kind")
    name := ← stringField json "name"
    runId := ← fromJson? (← field json "runId")
    model? := ← optionalStringField json "model"
    configuration? := ← optionalStringField json "configuration"
  }

def EvaluationOutcome.toString : EvaluationOutcome → String
  | .accepted => "accepted" | .rejected => "rejected" | .timedOut => "timed-out"
  | .resourceExhausted => "resource-exhausted"

def EvaluationOutcome.ofString (value : String) : Except String EvaluationOutcome :=
  match value with
  | "accepted" => .ok .accepted | "rejected" => .ok .rejected
  | "timed-out" => .ok .timedOut | "resource-exhausted" => .ok .resourceExhausted
  | _ => .error s!"unknown evaluation outcome '{value}'"

private def payloadDataJson : Payload → Json
  | .attemptCreated value => Json.mkObj [
      ("title", toJson value.title), ("goal", toJson value.goal),
      ("initialStateId", optionJson value.initialStateId?),
      ("parentAttemptId", optionJson value.parentAttemptId?)]
  | .retrievalPerformed value => Json.mkObj [
      ("retrievalId", toJson value.retrievalId), ("query", toJson value.query),
      ("results", toJson value.results)]
  | .actionProposed value => Json.mkObj [
      ("stateId", toJson value.stateId), ("action", toJson value.action),
      ("retrievalIds", toJson value.retrievalIds)]
  | .actionEvaluated value => Json.mkObj [
      ("transitionId", toJson value.transitionId),
      ("parentStateId", toJson value.parentStateId),
      ("childStateId", optionJson value.childStateId?), ("action", toJson value.action),
      ("outcome", toJson value.outcome.toString), ("goals", toJson value.goals),
      ("diagnostics", toJson value.diagnostics),
      ("usedDeclarations", toJson value.usedDeclarations), ("complete", toJson value.complete),
      ("wallMs", optionJson value.wallMs?), ("heartbeats", optionJson value.heartbeats?)]
  | .branchSelected value => Json.mkObj [
      ("stateId", toJson value.stateId), ("reason", optionJson value.reason?)]
  | .branchAbandoned value => Json.mkObj [
      ("stateId", toJson value.stateId), ("reason", toJson value.reason)]
  | .artifactChecked value => Json.mkObj [
      ("artifact", toJson value.artifact), ("clean", toJson value.clean),
      ("declarations", toJson value.declarations), ("errors", toJson value.errors),
      ("diagnostics", toJson value.diagnostics)]
  | .policyRejected value => Json.mkObj [
      ("artifact", toJson value.artifact), ("violations", toJson value.violations)]
  | .artifactPromoted value => Json.mkObj [
      ("artifact", toJson value.artifact), ("catalogId", toJson value.catalogId)]

private def optionalIdField [FromJson α] (json : Json) (key : String) : Except String (Option α) := do
  match ← field json key with
  | .null => return none
  | value => return some (← fromJson? value)

private def idArrayField [FromJson α] (json : Json) (key : String) : Except String (Array α) := do
  let values ← match (← field json key).getArr? with
    | .ok values => pure values
    | .error _ => throw s!"field '{key}' must be an array"
  values.mapM fromJson?

def payloadOfJson (kind : String) (json : Json) : Except String Payload :=
  match kind with
  | "attempt.created" => do
      exactObject json ["title", "goal", "initialStateId", "parentAttemptId"]
      return .attemptCreated {
        title := ← stringField json "title", goal := ← stringField json "goal"
        initialStateId? := ← optionalIdField json "initialStateId"
        parentAttemptId? := ← optionalIdField json "parentAttemptId" }
  | "retrieval.performed" => do
      exactObject json ["retrievalId", "query", "results"]
      return .retrievalPerformed {
        retrievalId := ← fromJson? (← field json "retrievalId")
        query := ← stringField json "query", results := ← stringArrayField json "results" }
  | "action.proposed" => do
      exactObject json ["stateId", "action", "retrievalIds"]
      return .actionProposed {
        stateId := ← fromJson? (← field json "stateId"), action := ← stringField json "action"
        retrievalIds := ← idArrayField json "retrievalIds" }
  | "action.evaluated" => do
      exactObject json ["transitionId", "parentStateId", "childStateId", "action", "outcome",
        "goals", "diagnostics", "usedDeclarations", "complete", "wallMs", "heartbeats"]
      return .actionEvaluated {
        transitionId := ← fromJson? (← field json "transitionId")
        parentStateId := ← fromJson? (← field json "parentStateId")
        childStateId? := ← optionalIdField json "childStateId"
        action := ← stringField json "action"
        outcome := ← EvaluationOutcome.ofString (← stringField json "outcome")
        goals := ← stringArrayField json "goals"
        diagnostics := ← stringArrayField json "diagnostics"
        usedDeclarations := ← stringArrayField json "usedDeclarations"
        complete := ← boolField json "complete"
        wallMs? := ← optionalNatField json "wallMs"
        heartbeats? := ← optionalNatField json "heartbeats" }
  | "branch.selected" => do
      exactObject json ["stateId", "reason"]
      let stateId : ProofStateId ← fromJson? (← field json "stateId")
      let reason? ← optionalStringField json "reason"
      return .branchSelected { stateId, reason? }
  | "branch.abandoned" => do
      exactObject json ["stateId", "reason"]
      let stateId : ProofStateId ← fromJson? (← field json "stateId")
      let reason ← stringField json "reason"
      return .branchAbandoned { stateId, reason }
  | "artifact.checked" => do
      exactObject json ["artifact", "clean", "declarations", "errors", "diagnostics"]
      return .artifactChecked {
        artifact := ← stringField json "artifact"
        clean := ← boolField json "clean"
        declarations := ← natField json "declarations"
        errors := ← stringArrayField json "errors"
        diagnostics := ← stringArrayField json "diagnostics" }
  | "policy.rejected" => do
      exactObject json ["artifact", "violations"]
      let artifact ← stringField json "artifact"
      let violations ← stringArrayField json "violations"
      return .policyRejected { artifact, violations }
  | "artifact.promoted" => do
      exactObject json ["artifact", "catalogId"]
      let artifact ← stringField json "artifact"
      let catalogId ← stringField json "catalogId"
      return .artifactPromoted { artifact, catalogId }
  | _ => .error s!"unknown event kind '{kind}'"

def eventJson (event : Event) : Json := Json.mkObj [
  ("schemaVersion", toJson event.schemaVersion),
  ("trusted", toJson false),
  ("eventId", toJson event.eventId),
  ("attemptId", toJson event.attemptId),
  ("sequence", toJson event.sequence),
  ("occurredAt", toJson event.occurredAt),
  ("environment", environmentJson event.environment),
  ("actor", actorJson event.actor),
  ("kind", toJson event.payload.kind),
  ("payload", payloadDataJson event.payload)
]

def eventOfJson (json : Json) : Except String Event := do
  exactObject json ["schemaVersion", "trusted", "eventId", "attemptId", "sequence", "occurredAt",
    "environment", "actor", "kind", "payload"]
  let version ← natField json "schemaVersion"
  unless version == 1 do throw s!"unsupported research event schema version {version}"
  let trusted ← boolField json "trusted"
  if trusted then throw "research events must declare trusted=false"
  let kind ← stringField json "kind"
  return {
    schemaVersion := version
    eventId := ← fromJson? (← field json "eventId")
    attemptId := ← fromJson? (← field json "attemptId")
    sequence := ← natField json "sequence"
    occurredAt := ← stringField json "occurredAt"
    environment := ← environmentOfJson (← field json "environment")
    actor := ← actorOfJson (← field json "actor")
    payload := ← payloadOfJson kind (← field json "payload")
  }

instance : ToJson Event := ⟨eventJson⟩
instance : FromJson Event := ⟨eventOfJson⟩

end Frontier.Research
