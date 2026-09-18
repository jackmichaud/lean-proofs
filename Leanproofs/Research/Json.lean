/-
Copyright (c) 2026 Jack Michaud. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Michaud
-/

import Leanproofs.Research.Model

namespace Frontier.Research

open Lean

private def exactObject (json : Json) (expected : List String) : Except String Unit := do
  let fields ← json.getObj?
  let actual := fields.foldl (init := []) fun keys key _ => key :: keys
  let unexpected := actual.filter fun key => !expected.contains key
  let missing := expected.filter fun key => !actual.contains key
  unless unexpected.isEmpty do throw s!"unexpected field(s): {", ".intercalate unexpected}"
  unless missing.isEmpty do throw s!"missing field(s): {", ".intercalate missing}"

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
  | value => match value.getStr? with
    | .ok text => return some text
    | .error _ => throw s!"field '{key}' must be a string or null"

private def optionalNatField (json : Json) (key : String) : Except String (Option Nat) := do
  match ← field json key with
  | .null => return none
  | value => match value.getNat? with
    | .ok number => return some number
    | .error _ => throw s!"field '{key}' must be a non-negative integer or null"

private def stringArrayField (json : Json) (key : String) : Except String (Array String) := do
  let values ← match (← field json key).getArr? with
    | .ok values => pure values
    | .error _ => throw s!"field '{key}' must be an array"
  values.mapM fun element => match element.getStr? with
    | .ok text => pure text
    | .error _ => throw s!"field '{key}' must contain only strings"

private def optionJson [ToJson α] : Option α → Json
  | none => .null | some value => toJson value

instance : ToJson AttemptId := ⟨fun id => toJson id.value⟩
instance : ToJson ProofStateId := ⟨fun id => toJson id.value⟩
instance : ToJson TransitionId := ⟨fun id => toJson id.value⟩
instance : ToJson RetrievalId := ⟨fun id => toJson id.value⟩
instance : ToJson RunId := ⟨fun id => toJson id.value⟩
instance : ToJson EventId := ⟨fun id => toJson id.value⟩

private def parseId (kind : String) (parse : String → Except String α) (json : Json) : Except String α := do
  let value ← match json.getStr? with
    | .ok value => pure value | .error _ => throw s!"{kind} must be a string"
  parse value

instance : FromJson AttemptId := ⟨parseId "attempt id" AttemptId.parse⟩
instance : FromJson ProofStateId := ⟨parseId "proof state id" ProofStateId.parse⟩
instance : FromJson TransitionId := ⟨parseId "transition id" TransitionId.parse⟩
instance : FromJson RetrievalId := ⟨parseId "retrieval id" RetrievalId.parse⟩
instance : FromJson RunId := ⟨parseId "run id" RunId.parse⟩
instance : FromJson EventId := ⟨parseId "event id" EventId.parse⟩

def environmentJson (value : EnvironmentFingerprint) : Json := Json.mkObj [
  ("leanVersion", toJson value.leanVersion), ("mathlibRevision", toJson value.mathlibRevision),
  ("frontierRevision", toJson value.frontierRevision), ("importsHash", toJson value.importsHash),
  ("policyVersion", toJson value.policyVersion)]

def environmentOfJson (json : Json) : Except String EnvironmentFingerprint := do
  exactObject json ["leanVersion", "mathlibRevision", "frontierRevision", "importsHash", "policyVersion"]
  return {
    leanVersion := ← stringField json "leanVersion"
    mathlibRevision := ← stringField json "mathlibRevision"
    frontierRevision := ← stringField json "frontierRevision"
    importsHash := ← stringField json "importsHash"
    policyVersion := ← stringField json "policyVersion" }

def ActorKind.toString : ActorKind → String
  | .human => "human" | .agent => "agent" | .tool => "tool" | .system => "system"

def ActorKind.ofString : String → Except String ActorKind
  | "human" => .ok .human | "agent" => .ok .agent | "tool" => .ok .tool
  | "system" => .ok .system | value => .error s!"unknown actor kind '{value}'"

def actorJson (value : Actor) : Json := Json.mkObj [
  ("kind", toJson value.kind.toString), ("name", toJson value.name),
  ("runId", toJson value.runId), ("model", optionJson value.model?),
  ("configuration", optionJson value.configuration?)]

def actorOfJson (json : Json) : Except String Actor := do
  exactObject json ["kind", "name", "runId", "model", "configuration"]
  return {
    kind := ← ActorKind.ofString (← stringField json "kind")
    name := ← stringField json "name"
    runId := ← fromJson? (← field json "runId")
    model? := ← optionalStringField json "model"
    configuration? := ← optionalStringField json "configuration" }

def EvaluationOutcome.toString : EvaluationOutcome → String
  | .accepted => "accepted" | .rejected => "rejected" | .timedOut => "timed-out"
  | .resourceExhausted => "resource-exhausted"

def EvaluationOutcome.ofString : String → Except String EvaluationOutcome
  | "accepted" => .ok .accepted | "rejected" => .ok .rejected
  | "timed-out" => .ok .timedOut | "resource-exhausted" => .ok .resourceExhausted
  | value => .error s!"unknown evaluation outcome '{value}'"

private def metadataJson (value : WorkMetadata) : Json := Json.mkObj [
  ("title", toJson value.title), ("goal", toJson value.goal),
  ("draftPath", optionJson value.draftPath?), ("note", optionJson value.note?)]

private def metadataOfJson (json : Json) : Except String WorkMetadata := do
  exactObject json ["title", "goal", "draftPath", "note"]
  return {
    title := ← stringField json "title"
    goal := ← stringField json "goal"
    draftPath? := ← optionalStringField json "draftPath"
    note? := ← optionalStringField json "note" }

private def optionalIdField [FromJson α] (json : Json) (key : String) : Except String (Option α) := do
  match ← field json key with | .null => return none | value => return some (← fromJson? value)

private def idArrayField [FromJson α] (json : Json) (key : String) : Except String (Array α) := do
  let values ← match (← field json key).getArr? with
    | .ok values => pure values | .error _ => throw s!"field '{key}' must be an array"
  values.mapM fromJson?

private def payloadDataJson : Payload → Json
  | .attemptCreated v => Json.mkObj [("metadata", metadataJson v.metadata),
      ("initialStateId", optionJson v.initialStateId?), ("proposition", optionJson v.proposition?),
      ("parentAttemptId", optionJson v.parentAttemptId?)]
  | .metadataUpdated v => Json.mkObj [("metadata", metadataJson v.metadata)]
  | .stageChanged v => Json.mkObj [("from", toJson v.fromStage.toString), ("to", toJson v.toStage.toString),
      ("reason", optionJson v.reason?)]
  | .retrievalPerformed v => Json.mkObj [("retrievalId", toJson v.retrievalId),
      ("query", toJson v.query), ("results", toJson v.results)]
  | .actionProposed v => Json.mkObj [("stateId", toJson v.stateId), ("action", toJson v.action),
      ("retrievalIds", toJson v.retrievalIds)]
  | .actionEvaluated v => Json.mkObj [("transitionId", toJson v.transitionId),
      ("parentStateId", toJson v.parentStateId), ("childStateId", optionJson v.childStateId?),
      ("action", toJson v.action), ("outcome", toJson v.outcome.toString), ("goals", toJson v.goals),
      ("diagnostics", toJson v.diagnostics), ("usedDeclarations", toJson v.usedDeclarations),
      ("complete", toJson v.complete), ("wallMs", optionJson v.wallMs?),
      ("heartbeats", optionJson v.heartbeats?)]
  | .branchSelected v => Json.mkObj [("stateId", toJson v.stateId), ("reason", optionJson v.reason?)]
  | .branchAbandoned v => Json.mkObj [("stateId", toJson v.stateId), ("reason", toJson v.reason)]
  | .artifactChecked v => Json.mkObj [("artifact", toJson v.artifact), ("clean", toJson v.clean),
      ("declarations", toJson v.declarations), ("reuses", toJson v.reuses), ("axioms", toJson v.axioms),
      ("errors", toJson v.errors), ("diagnostics", toJson v.diagnostics)]
  | .policyRejected v => Json.mkObj [("artifact", toJson v.artifact), ("violations", toJson v.violations)]
  | .artifactPromoted v => Json.mkObj [("artifact", toJson v.artifact), ("catalogId", toJson v.catalogId)]

def payloadOfJson (kind : String) (json : Json) : Except String Payload := do
  match kind with
  | "attempt.created" =>
      exactObject json ["metadata", "initialStateId", "proposition", "parentAttemptId"]
      return .attemptCreated {
        metadata := ← metadataOfJson (← field json "metadata")
        initialStateId? := ← optionalIdField json "initialStateId"
        proposition? := ← optionalStringField json "proposition"
        parentAttemptId? := ← optionalIdField json "parentAttemptId" }
  | "attempt.metadata-updated" =>
      exactObject json ["metadata"]
      return .metadataUpdated { metadata := ← metadataOfJson (← field json "metadata") }
  | "attempt.stage-changed" =>
      exactObject json ["from", "to", "reason"]
      return .stageChanged {
        fromStage := ← Stage.ofString (← stringField json "from")
        toStage := ← Stage.ofString (← stringField json "to")
        reason? := ← optionalStringField json "reason" }
  | "retrieval.performed" =>
      exactObject json ["retrievalId", "query", "results"]
      return .retrievalPerformed {
        retrievalId := ← fromJson? (← field json "retrievalId")
        query := ← stringField json "query"
        results := ← stringArrayField json "results" }
  | "action.proposed" =>
      exactObject json ["stateId", "action", "retrievalIds"]
      return .actionProposed {
        stateId := ← fromJson? (← field json "stateId")
        action := ← stringField json "action"
        retrievalIds := ← idArrayField json "retrievalIds" }
  | "action.evaluated" =>
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
  | "branch.selected" =>
      exactObject json ["stateId", "reason"]
      return .branchSelected {
        stateId := ← fromJson? (← field json "stateId")
        reason? := ← optionalStringField json "reason" }
  | "branch.abandoned" =>
      exactObject json ["stateId", "reason"]
      return .branchAbandoned {
        stateId := ← fromJson? (← field json "stateId")
        reason := ← stringField json "reason" }
  | "artifact.checked" =>
      exactObject json ["artifact", "clean", "declarations", "reuses", "axioms", "errors", "diagnostics"]
      return .artifactChecked {
        artifact := ← stringField json "artifact"
        clean := ← boolField json "clean"
        declarations := ← natField json "declarations"
        reuses := ← stringArrayField json "reuses"
        axioms := ← stringArrayField json "axioms"
        errors := ← stringArrayField json "errors"
        diagnostics := ← stringArrayField json "diagnostics" }
  | "policy.rejected" =>
      exactObject json ["artifact", "violations"]
      return .policyRejected {
        artifact := ← stringField json "artifact"
        violations := ← stringArrayField json "violations" }
  | "artifact.promoted" =>
      exactObject json ["artifact", "catalogId"]
      return .artifactPromoted {
        artifact := ← stringField json "artifact"
        catalogId := ← stringField json "catalogId" }
  | _ => throw s!"unknown event kind '{kind}'"

def eventJson (event : Event) : Json := Json.mkObj [
  ("schemaVersion", toJson event.schemaVersion), ("trusted", toJson false),
  ("eventId", toJson event.eventId), ("attemptId", toJson event.attemptId),
  ("sequence", toJson event.sequence), ("occurredAt", toJson event.occurredAt),
  ("environment", environmentJson event.environment), ("actor", actorJson event.actor),
  ("kind", toJson event.payload.kind), ("payload", payloadDataJson event.payload)]

def eventOfJson (json : Json) : Except String Event := do
  exactObject json ["schemaVersion", "trusted", "eventId", "attemptId", "sequence", "occurredAt",
    "environment", "actor", "kind", "payload"]
  let version ← natField json "schemaVersion"
  unless version == 3 do throw s!"unsupported research event schema version {version}"
  if ← boolField json "trusted" then throw "research events must declare trusted=false"
  let kind ← stringField json "kind"
  return {
    schemaVersion := version
    eventId := ← fromJson? (← field json "eventId")
    attemptId := ← fromJson? (← field json "attemptId")
    sequence := ← natField json "sequence"
    occurredAt := ← stringField json "occurredAt"
    environment := ← environmentOfJson (← field json "environment")
    actor := ← actorOfJson (← field json "actor")
    payload := ← payloadOfJson kind (← field json "payload") }

instance : ToJson Event := ⟨eventJson⟩
instance : FromJson Event := ⟨eventOfJson⟩

end Frontier.Research
