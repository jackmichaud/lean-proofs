/-
Copyright (c) 2026 Jack Michaud. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Michaud
-/

import Leanproofs.Research.Json

namespace Frontier.Research

open Lean

def streamPath (root : System.FilePath) (attemptId : AttemptId) : Except String System.FilePath := do
  let value ← validateIdValue "attempt id" attemptId.value
  return root / s!"{value}.jsonl"

private def parseLine (path : System.FilePath) (lineNumber : Nat) (line : String) : Except String Event := do
  let json ← match Json.parse line with
    | .ok json => pure json
    | .error message => throw s!"{path}:{lineNumber}: invalid JSON: {message}"
  match eventOfJson json with
  | .ok event => return event
  | .error message => throw s!"{path}:{lineNumber}: {message}"

private def parseDigits (chars : List Char) : Option Nat :=
  if chars.all (fun c => c.isDigit && c.toNat < 128) then (String.ofList chars).toNat?
  else none

private def leapYear (year : Nat) : Bool :=
  year % 400 == 0 || (year % 4 == 0 && year % 100 != 0)

private def daysInMonth (year month : Nat) : Nat :=
  match month with
  | 2 => if leapYear year then 29 else 28
  | 4 | 6 | 9 | 11 => 30
  | _ => 31

/-- Validate the canonical UTC form emitted by Frontier: `YYYY-MM-DDTHH:MM:SSZ`. Keeping one
fixed-width form also makes lexical order equal chronological order. -/
def validateTimestamp (value : String) : Except String Unit := do
  let fail : Except String Unit := .error s!"invalid UTC timestamp '{value}'; expected YYYY-MM-DDTHH:MM:SSZ"
  match value.toList with
  | [y1, y2, y3, y4, '-', m1, m2, '-', d1, d2, 'T', h1, h2, ':', n1, n2, ':', s1, s2, 'Z'] =>
      let some year := parseDigits [y1, y2, y3, y4] | fail
      let some month := parseDigits [m1, m2] | fail
      let some day := parseDigits [d1, d2] | fail
      let some hour := parseDigits [h1, h2] | fail
      let some minute := parseDigits [n1, n2] | fail
      let some second := parseDigits [s1, s2] | fail
      unless month >= 1 && month <= 12 && day >= 1 && day <= daysInMonth year month &&
          hour < 24 && minute < 60 && second < 60 do fail
  | _ => fail

private def nonempty (label value : String) : Except String Unit :=
  unless !value.trimAscii.isEmpty do throw s!"{label} must not be empty"

private def validateMetadata (metadata : WorkMetadata) : Except String Unit := do
  nonempty "work title" metadata.title
  if let some path := metadata.draftPath? then nonempty "draft path" path
  if let some note := metadata.note? then nonempty "note" note

private def validateEnvironment (environment : EnvironmentFingerprint) : Except String Unit := do
  nonempty "Lean version" environment.leanVersion
  nonempty "mathlib revision" environment.mathlibRevision
  nonempty "Frontier revision" environment.frontierRevision
  nonempty "imports hash" environment.importsHash
  nonempty "policy version" environment.policyVersion

private def validateEventValues (event : Event) : Except String Unit := do
  unless event.schemaVersion == 2 do throw s!"unsupported research event schema version {event.schemaVersion}"
  let _ ← validateIdValue "event id" event.eventId.value
  let _ ← validateIdValue "attempt id" event.attemptId.value
  let _ ← validateIdValue "run id" event.actor.runId.value
  validateTimestamp event.occurredAt
  validateEnvironment event.environment
  nonempty "actor name" event.actor.name
  match event.payload with
  | .attemptCreated value =>
      validateMetadata value.metadata
      if let some id := value.initialStateId? then let _ ← validateIdValue "proof state id" id.value
      if let some id := value.parentAttemptId? then
        let _ ← validateIdValue "parent attempt id" id.value
        if id == event.attemptId then throw "an attempt cannot be its own parent"
  | .metadataUpdated value => validateMetadata value.metadata
  | .stageChanged value =>
      if value.fromStage == value.toStage then throw "a stage transition must change stage"
      if value.toStage == .clean || value.toStage == .registered then
        throw s!"stage '{value.toStage.toString}' is derived and cannot be asserted by stage change"
      if value.toStage == .blocked || value.toStage == .abandoned then
        match value.reason? with
        | some reason => nonempty "stage transition reason" reason
        | none => throw s!"stage '{value.toStage.toString}' requires a reason"
  | .retrievalPerformed value =>
      let _ ← validateIdValue "retrieval id" value.retrievalId.value
      nonempty "retrieval query" value.query
  | .actionProposed value =>
      let _ ← validateIdValue "proof state id" value.stateId.value
      nonempty "proposed action" value.action
      for id in value.retrievalIds do let _ ← validateIdValue "retrieval id" id.value
  | .actionEvaluated value =>
      let _ ← validateIdValue "transition id" value.transitionId.value
      let _ ← validateIdValue "parent state id" value.parentStateId.value
      if let some id := value.childStateId? then let _ ← validateIdValue "child state id" id.value
      nonempty "evaluated action" value.action
      if value.outcome == .accepted && value.childStateId?.isNone then
        throw "an accepted action must produce a child state"
      if value.outcome != .accepted && value.childStateId?.isSome then
        throw "a non-accepted action cannot produce a child state"
      if value.complete && value.outcome != .accepted then
        throw "only an accepted action can be complete"
  | .branchSelected value => let _ ← validateIdValue "proof state id" value.stateId.value
  | .branchAbandoned value =>
      let _ ← validateIdValue "proof state id" value.stateId.value
      nonempty "branch abandonment reason" value.reason
  | .artifactChecked value => nonempty "checked artifact" value.artifact
  | .policyRejected value =>
      nonempty "rejected artifact" value.artifact
      unless !value.violations.isEmpty do throw "a policy rejection must contain a violation"
  | .artifactPromoted value =>
      nonempty "promoted artifact" value.artifact
      nonempty "catalog id" value.catalogId

private def isAttemptCreated : Payload → Bool
  | .attemptCreated _ => true | _ => false

/-- Validate all stream invariants independently of filesystem IO. Besides framing, this checks
environment pinning, state/retrieval ownership, chronological order, and legal work stages. -/
def validateStream (attemptId : AttemptId) (events : Array Event) : Except String Unit := do
  let _ ← validateIdValue "attempt id" attemptId.value
  let mut eventIds : Std.HashSet EventId := {}
  let mut transitionIds : Std.HashSet TransitionId := {}
  let mut retrievalIds : Std.HashSet RetrievalId := {}
  let mut stateIds : Std.HashSet ProofStateId := {}
  let mut environment? : Option EnvironmentFingerprint := none
  let mut timestamp? : Option String := none
  let mut stage := Stage.exploring
  let mut promoted := false
  for index in [:events.size] do
    let event := events[index]!
    validateEventValues event
    let expected := index + 1
    unless event.attemptId == attemptId do
      throw s!"event {event.eventId.value} belongs to attempt '{event.attemptId.value}', expected '{attemptId.value}'"
    unless event.sequence == expected do
      throw s!"event {event.eventId.value} has sequence {event.sequence}, expected {expected}"
    if eventIds.contains event.eventId then throw s!"duplicate event id '{event.eventId.value}'"
    eventIds := eventIds.insert event.eventId
    match environment? with
    | none => environment? := some event.environment
    | some pinned => unless event.environment == pinned do throw "attempt environment changed within one stream"
    if let some previous := timestamp? then
      unless previous <= event.occurredAt do throw s!"event timestamp '{event.occurredAt}' precedes '{previous}'"
    timestamp? := some event.occurredAt
    if index == 0 then
      unless isAttemptCreated event.payload do throw "the first event in an attempt stream must be attempt.created"
    else if isAttemptCreated event.payload then throw "attempt.created may only be the first event in a stream"
    match event.payload with
    | .attemptCreated value =>
        stage := if value.metadata.draftPath?.isSome then .drafting else .exploring
        if let some id := value.initialStateId? then stateIds := stateIds.insert id
    | .metadataUpdated _ => pure ()
    | .stageChanged value =>
        unless value.fromStage == stage do
          throw s!"stage transition starts at '{value.fromStage.toString}', current stage is '{stage.toString}'"
        if stage == .registered then throw "a registered attempt cannot change stage"
        stage := value.toStage
    | .retrievalPerformed value =>
        if retrievalIds.contains value.retrievalId then throw s!"duplicate retrieval id '{value.retrievalId.value}'"
        retrievalIds := retrievalIds.insert value.retrievalId
    | .actionProposed value =>
        unless stateIds.contains value.stateId do throw s!"unknown proof state '{value.stateId.value}'"
        for id in value.retrievalIds do
          unless retrievalIds.contains id do throw s!"unknown retrieval id '{id.value}'"
    | .actionEvaluated value =>
        unless stateIds.contains value.parentStateId do throw s!"unknown parent state '{value.parentStateId.value}'"
        if transitionIds.contains value.transitionId then throw s!"duplicate transition id '{value.transitionId.value}'"
        transitionIds := transitionIds.insert value.transitionId
        if let some child := value.childStateId? then
          if stateIds.contains child then throw s!"duplicate proof state id '{child.value}'"
          stateIds := stateIds.insert child
    | .branchSelected value =>
        unless stateIds.contains value.stateId do throw s!"unknown proof state '{value.stateId.value}'"
    | .branchAbandoned value =>
        unless stateIds.contains value.stateId do throw s!"unknown proof state '{value.stateId.value}'"
    | .artifactChecked value =>
        if stage != .registered && stage != .abandoned then
          stage := if value.clean then .clean else .drafting
    | .policyRejected _ => pure ()
    | .artifactPromoted _ =>
        unless stage == .clean do throw "only a clean attempt can be promoted"
        if promoted then throw "an attempt may only be promoted once"
        promoted := true
        stage := .registered

/-- Read and validate one attempt's JSONL stream. Every physical nonterminal line is an event. -/
def readEvents (root : System.FilePath) (attemptId : AttemptId) : IO (Except String (Array Event)) := do
  let path ← match streamPath root attemptId with | .ok path => pure path | .error e => return .error e
  unless ← path.pathExists do return .ok #[]
  let contents ← IO.FS.readFile path
  let lines := if contents.endsWith "\n" then (contents.splitOn "\n").dropLast else contents.splitOn "\n"
  let mut events := #[]
  for index in [:lines.length] do
    let line := lines[index]!
    if line.isEmpty then return .error s!"{path}:{index + 1}: blank lines are not allowed"
    match parseLine path (index + 1) line with
    | .ok event => events := events.push event
    | .error message => return .error message
  match validateStream attemptId events with
  | .ok _ => return .ok events
  | .error message => return .error s!"{path}: {message}"

/-- Append exactly one event. This is a single-writer API: callers must serialize writers to a
stream. It validates existing bytes and never edits or deletes an earlier event. -/
def appendEvent (root : System.FilePath) (attemptId : AttemptId) (event : Event) : IO (Except String Unit) := do
  let path ← match streamPath root attemptId with | .ok path => pure path | .error e => return .error e
  let existing ← match ← readEvents root attemptId with | .ok es => pure es | .error e => return .error e
  match validateStream attemptId (existing.push event) with | .error e => return .error e | .ok _ => pure ()
  IO.FS.createDirAll root
  let handle ← IO.FS.Handle.mk path .append
  handle.putStr (eventJson event).compress
  handle.putStr "\n"
  handle.flush
  return .ok ()

/-- List and validate every attempt stream. Unrelated files are ignored; malformed `.jsonl`
stream names or contents fail the listing so authoritative history is never silently omitted. -/
def listAttemptIds (root : System.FilePath) : IO (Except String (Array AttemptId)) := do
  unless ← root.pathExists do return .ok #[]
  let mut ids := #[]
  for entry in ← root.readDir do
    let name := entry.fileName
    if name.endsWith ".jsonl" then
      let stem := String.ofList (name.toList.take (name.length - 6))
      let id ← match AttemptId.parse stem with
        | .ok id => pure id
        | .error message => return .error s!"{entry.path}: {message}"
      match ← readEvents root id with
      | .ok _ => ids := ids.push id
      | .error message => return .error message
  return .ok (ids.qsort fun a b => a.value < b.value)

end Frontier.Research
