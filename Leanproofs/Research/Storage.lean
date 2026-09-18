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

private def isAttemptCreated : Payload → Bool
  | .attemptCreated _ => true
  | _ => false

/-- Validate the stream invariants independently of filesystem IO. -/
def validateStream (attemptId : AttemptId) (events : Array Event) : Except String Unit := do
  let _ ← validateIdValue "attempt id" attemptId.value
  let mut seen : Std.HashSet EventId := {}
  for index in [:events.size] do
    let event := events[index]!
    let expected := index + 1
    unless event.attemptId == attemptId do
      throw s!"event {event.eventId.value} belongs to attempt '{event.attemptId.value}', expected '{attemptId.value}'"
    unless event.sequence == expected do
      throw s!"event {event.eventId.value} has sequence {event.sequence}, expected {expected}"
    if seen.contains event.eventId then
      throw s!"duplicate event id '{event.eventId.value}'"
    seen := seen.insert event.eventId
  if let some first := events[0]? then
    unless isAttemptCreated first.payload do
      throw "the first event in an attempt stream must be attempt.created"
  for event in events.drop 1 do
    if isAttemptCreated event.payload then
      throw "attempt.created may only be the first event in a stream"

/-- Read and validate one attempt's JSONL stream. Blank lines are rejected: every physical
line is part of the append-only record and therefore must be an event. -/
def readEvents (root : System.FilePath) (attemptId : AttemptId) : IO (Except String (Array Event)) := do
  let path ← match streamPath root attemptId with
    | .ok path => pure path
    | .error message => return .error message
  unless ← path.pathExists do return .ok #[]
  let contents ← IO.FS.readFile path
  let lines := contents.splitOn "\n"
  let lines := if contents.endsWith "\n" then lines.dropLast else lines
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

/-- Append exactly one event after validating the complete existing stream and the next
sequence number. This API never edits or deletes prior events. Concurrent writers must be
serialized by the future coordinator; the local filesystem API does not claim cross-process
locking. -/
def appendEvent (root : System.FilePath) (attemptId : AttemptId) (event : Event) : IO (Except String Unit) := do
  let path ← match streamPath root attemptId with
    | .ok path => pure path
    | .error message => return .error message
  let existing ← match ← readEvents root attemptId with
    | .ok events => pure events
    | .error message => return .error message
  unless event.attemptId == attemptId do
    return .error s!"event attempt '{event.attemptId.value}' does not match stream '{attemptId.value}'"
  let expected := existing.size + 1
  unless event.sequence == expected do
    return .error s!"event sequence {event.sequence} is not next; expected {expected}"
  if existing.any (·.eventId == event.eventId) then
    return .error s!"duplicate event id '{event.eventId.value}'"
  let candidate := existing.push event
  match validateStream attemptId candidate with
  | .error message => return .error message
  | .ok _ => pure ()
  IO.FS.createDirAll root
  let handle ← IO.FS.Handle.mk path .append
  handle.putStr (eventJson event).compress
  handle.putStr "\n"
  handle.flush
  return .ok ()

end Frontier.Research
