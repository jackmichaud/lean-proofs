/-
Copyright (c) 2026 Jack Michaud. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Michaud
-/

import Leanproofs.Frontier.Command

open Lean

namespace Frontier.CLI

private def workEnvironment (context : Context) : Research.EnvironmentFingerprint :=
  context.fingerprint.environment

private def workActor : Research.Actor := {
  kind := .tool
  name := "frontier-cli"
  runId := ⟨"frontier-cli-local"⟩
  configuration? := some "local invocation; caller and model identity unavailable"
}

private def publishWork (context : Context) : IO Unit := do
  if let some path := context.workPublish? then
    _ ← Journal.publish context.workRoot path

/-- Append one research event batch under the active Frontier environment, then refresh the
materialized web view. The batch is all-or-nothing with respect to validation. -/
def appendResearch (context : Context) (id : String) (actor : Research.Actor)
    (payloads : Array Research.Payload) : IO (Except String Journal.Item) := do
  match ← Journal.appendMany context.workRoot id (workEnvironment context) actor payloads with
  | .error message => return .error message
  | .ok item =>
      publishWork context
      return .ok item

private def appendWork (context : Context) (id : String) (payload : Research.Payload) :
    IO (Except Payload Journal.Item) := do
  match ← appendResearch context id workActor #[payload] with
  | .error message => return .error (.failure message)
  | .ok item => return .ok item

def loadItem (context : Context) (id : String) : IO (Except Payload Journal.Item) := do
  if !Journal.isValidId id then
    return .error (.failure s!"'{id}' is not a valid work item id; ids are lowercase alphanumerics and hyphens")
  match ← Journal.read? context.workRoot id with
  | .error message => return .error (.failure message)
  | .ok item => return .ok item

def workList (context : Context) (stage? : Option String) : IO Payload := do
  let (items, problems) ← Journal.readAll context.workRoot
  match stage? with
  | none => return .work items problems
  | some text =>
      let some stage := Journal.Stage.ofString? text
        | return .failure s!"unknown stage '{text}'; expected one of {", ".intercalate Journal.stageNames.toList}"
      return .work (items.filter (·.stage == stage)) problems

def resolveDraft (draft : String) : IO (Except String String) := do
  if ← (draft : System.FilePath).pathExists then return .ok draft
  return .error s!"draft file '{draft}' does not exist"

def workAdd (context : Context) (title : String)
    (goal? draft? note? : Option String) : IO Payload := do
  if title.trimAscii.isEmpty then return .failure "a work item needs a title"
  let mut resolved := none
  if let some draft := draft? then
    match ← resolveDraft draft with
    | .error message => return .failure message
    | .ok path => resolved := some path
  let id ← Journal.freshId context.workRoot title
  let metadata : Research.WorkMetadata := {
    title := title.trimAscii.toString
    goal := (goal?.getD "").trimAscii.toString
    draftPath? := resolved
    note? := note?.bind fun note =>
      let trimmed := note.trimAscii.toString
      if trimmed.isEmpty then none else some trimmed
  }
  match ← appendWork context id (.attemptCreated { metadata }) with
  | .error payload => return payload
  | .ok item => return .workItem item s!"Added work item '{id}'."

def workShow (context : Context) (id : String) : IO Payload := do
  match ← loadItem context id with
  | .error payload => return payload
  | .ok item => return .workItem item ""

private def metadataOf (item : Journal.Item) : Research.WorkMetadata := {
  title := item.title
  goal := item.goal
  draftPath? := item.draft?
  note? := item.note?
}

def workSet (context : Context) (id : String)
    (stage? goal? draft? note? entry? : Option String) : IO Payload := do
  match ← loadItem context id with
  | .error payload => return payload
  | .ok original =>
      if entry?.isSome && stage? != some "registered" then
        return .failure "--entry is only valid with --stage registered"
      let requestedStage? ← match stage? with
        | none => pure none
        | some text =>
            let some stage := Journal.Stage.ofString? text
              | return .failure s!"unknown stage '{text}'; expected one of {", ".intercalate Journal.stageNames.toList}"
            match stage with
            | .clean => return .failure (stage.handSetError?.getD "")
            | .abandoned =>
                return .failure "use `frontier work abandon <id> --reason '<reason>'` to preserve why the work stopped"
            | .registered =>
                if original.stage != .clean then
                  return .failure "only work with a clean artifact check can be registered"
                let some entryId := entry?
                  | return .failure (stage.handSetError?.getD "")
                if (context.entry? entryId).isNone then
                  return .failure s!"no catalog entry '{entryId}'; `registered` requires one that exists"
                pure (some stage)
            | _ => pure (some stage)
      let mut metadata := metadataOf original
      if let some text := goal? then
        metadata := { metadata with goal := text.trimAscii.toString }
      if let some text := note? then
        let trimmed := text.trimAscii.toString
        metadata := { metadata with note? := if trimmed.isEmpty then none else some trimmed }
      if let some draft := draft? then
        match ← resolveDraft draft with
        | .error message => return .failure message
        | .ok path => metadata := { metadata with draftPath? := some path }
      let mut item := original
      if metadata != metadataOf original then
        match ← appendWork context id (.metadataUpdated { metadata }) with
        | .error payload => return payload
        | .ok updated => item := updated
      if let some stage := requestedStage? then
        match stage with
        | .registered =>
            let entryId := entry?.get!
            let entry := (context.entry? entryId).get!
            match ← appendWork context id (.artifactPromoted {
                artifact := entry.statement.toString, catalogId := entryId }) with
            | .error payload => return payload
            | .ok updated => item := updated
        | .clean | .abandoned => unreachable!
        | _ =>
            if stage != item.stage then
              let reason? := if stage == .blocked then item.note?.orElse (fun _ => some "marked blocked") else none
              match ← appendWork context id (.stageChanged {
                  fromStage := item.stage, toStage := stage, reason? }) with
              | .error payload => return payload
              | .ok updated => item := updated
      return .workItem item s!"Updated work item '{id}'."

def workAbandon (context : Context) (id reason : String) : IO Payload := do
  if reason.trimAscii.isEmpty then return .failure "work abandon requires a non-empty reason"
  match ← loadItem context id with
  | .error payload => return payload
  | .ok item =>
      if item.stage == .abandoned then return .failure s!"work item '{id}' is already abandoned"
      match ← appendWork context id (.stageChanged {
          fromStage := item.stage
          toStage := .abandoned
          reason? := some reason.trimAscii.toString }) with
      | .error payload => return payload
      | .ok updated => return .workAbandoned updated.id

def workExport (context : Context) (path : System.FilePath) : IO Payload := do
  let items ← Journal.publish context.workRoot path
  return .exported { path := path.toString, entries := items, valid := true }

def stageAfterCheck (current : Journal.Stage) (clean : Bool) : Journal.Stage :=
  if current == .registered || current == .abandoned then current
  else if clean then .clean else .drafting

def recordCheck (context : Context) (item : Journal.Item) (path : String)
    (report : DraftReport) : IO Journal.Item := do
  let union (get : DraftDeclaration → Array String) : Array String :=
    let collected := report.declarations.foldl (init := ({} : Std.HashSet String))
      fun set declaration => (get declaration).foldl (init := set) Std.HashSet.insert
    collected.toArray.qsort (· < ·)
  let checked : Research.ArtifactChecked := {
    artifact := path
    clean := report.isClean
    declarations := report.declarations.size
    reuses := union (·.dependencies)
    axioms := union (·.axioms.map Name.toString)
    errors := report.fatal ++ report.declarations.flatMap (·.errors)
    diagnostics := report.diagnostics
  }
  match ← appendWork context item.id (.artifactChecked checked) with
  | .ok updated => return updated
  | .error (.failure message) => throw <| IO.userError message
  | .error _ => throw <| IO.userError "failed to append artifact check"

end Frontier.CLI
