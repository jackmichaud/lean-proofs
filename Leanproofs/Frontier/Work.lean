/-
Copyright (c) 2026 Jack Michaud. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Michaud
-/

import Leanproofs.Frontier.Command

open Lean

namespace Frontier.CLI

/-! ### Work journal commands

Reading and writing JSON files. Nothing here elaborates, builds, or runs anything, which is
what makes a durable record of agent work available now rather than after the sandbox in
`docs/retrieval-and-agents.md` exists. -/

/-- Load an item, or a failure payload naming it. -/
def loadItem (context : Context) (id : String) : IO (Except Payload Journal.Item) := do
  if !Journal.isValidId id then
    -- An id becomes a filename. Rejecting the shape here is what keeps `work/../../x` from
    -- ever reaching the filesystem.
    return .error (.failure s!"'{id}' is not a valid work item id; \
      ids are lowercase alphanumerics and hyphens")
  match ← Journal.read? context.workRoot id with
  | .error message => return .error (.failure message)
  | .ok item => return .ok item

def saveItem (context : Context) (item : Journal.Item) (headline : String) : IO Payload := do
  let item := { item with updated := ← Journal.timestampNow }
  Journal.save context.workRoot context.workPublish? item
  return .workItem item headline

def workList (context : Context) (stage? : Option String) : IO Payload := do
  let (items, problems) ← Journal.readAll context.workRoot
  match stage? with
  | none => return .work items problems
  | some text =>
      let some stage := Journal.Stage.ofString? text
        | return .failure s!"unknown stage '{text}'; expected one of \
            {", ".intercalate Journal.stageNames.toList}"
      return .work (items.filter (·.stage == stage)) problems

/-- Record a draft path on an item, checking it exists.

A path that does not resolve is a typo that would otherwise sit in the journal until someone
wondered why `check --work` kept reporting a missing file. -/
def resolveDraft (draft : String) : IO (Except String String) := do
  if ← (draft : System.FilePath).pathExists then
    return .ok draft
  return .error s!"draft file '{draft}' does not exist"

def workAdd (context : Context) (title : String)
    (goal? draft? note? : Option String) : IO Payload := do
  if title.trimAscii.isEmpty then
    return .failure "a work item needs a title"
  let mut resolved := none
  if let some draft := draft? then
    match ← resolveDraft draft with
    | .error message => return .failure message
    | .ok path => resolved := some path
  let now ← Journal.timestampNow
  let id ← Journal.freshId context.workRoot title
  let item : Journal.Item := {
    id
    title := title.trimAscii.toString
    goal := (goal?.getD "").trimAscii.toString
    draft? := resolved
    note? := note?
    -- A brand-new item has a draft only if one was named; otherwise there is nothing to
    -- iterate on yet, and saying `drafting` would overstate it.
    stage := if resolved.isSome then .drafting else .exploring
    created := now
    updated := now
  }
  Journal.save context.workRoot context.workPublish? item
  return .workItem item s!"Added work item '{id}'."

def workShow (context : Context) (id : String) : IO Payload := do
  match ← loadItem context id with
  | .error payload => return payload
  | .ok item => return .workItem item ""

/-- Update fields on an item.

The interesting logic is the stage. `clean` and `registered` assert that something else is
true, so they are not writable the way a note is: the first is written by `check --work` from a
report that passed, and the second requires naming a catalog entry that exists. Without that,
the board would be a progress indicator anyone could fill in. -/
def workSet (context : Context) (id : String)
    (stage? goal? draft? note? entry? : Option String) : IO Payload := do
  match ← loadItem context id with
  | .error payload => return payload
  | .ok item =>
      let mut item := item
      if let some text := goal? then
        item := { item with goal := text.trimAscii.toString }
      if let some text := note? then
        -- An explicit empty value clears the note rather than storing "".
        item := { item with note? := if text.trimAscii.isEmpty then none else some text }
      if let some draft := draft? then
        match ← resolveDraft draft with
        | .error message => return .failure message
        | .ok path => item := { item with draft? := some path }
      if let some entry := entry? then
        if (context.entry? entry).isNone then
          return .failure s!"no catalog entry '{entry}'; \
            `--entry` must name a registered result (see `frontier list`)"
        item := { item with entry? := some entry }
      if let some text := stage? then
        let some stage := Journal.Stage.ofString? text
          | return .failure s!"unknown stage '{text}'; expected one of \
              {", ".intercalate Journal.stageNames.toList}"
        match stage with
        | .clean =>
            return .failure (stage.handSetError?.getD "")
        | .registered =>
            -- Allowed, but only against a catalog entry that exists. `entry?` on the item has
            -- already been validated above if it was supplied in this same call.
            let some entry := (entry?.orElse fun _ => item.entry?)
              | return .failure (stage.handSetError?.getD "")
            if (context.entry? entry).isNone then
              return .failure s!"no catalog entry '{entry}'; \
                `registered` requires one that exists"
            item := { item with stage := .registered, entry? := some entry }
        | _ => item := { item with stage }
      saveItem context item s!"Updated work item '{id}'."

def workRemove (context : Context) (id : String) : IO Payload := do
  match ← loadItem context id with
  | .error payload => return payload
  | .ok _ =>
      Journal.remove context.workRoot id
      if let some path := context.workPublish? then
        _ ← Journal.publish context.workRoot path
      return .workRemoved id

def workExport (context : Context) (path : System.FilePath) : IO Payload := do
  let items ← Journal.publish context.workRoot path
  return .exported { path := path.toString, entries := items, valid := true }

/-- The stage an item moves to after a check.

A previously `clean` item whose draft has broken must not stay `clean`; that is the one
transition the journal would be actively misleading without. `registered` and `abandoned` are
left alone, since a check against them is information rather than a state change. -/
def stageAfterCheck (current : Journal.Stage) (clean : Bool) : Journal.Stage :=
  match current with
  | .registered | .abandoned => current
  | _ => if clean then .clean else .drafting

/-- Fold a draft report into the item it was checked for. -/
def recordCheck (context : Context) (item : Journal.Item) (path : String)
    (report : DraftReport) : IO Journal.Item := do
  let union (get : DraftDeclaration → Array String) : Array String :=
    let collected := report.declarations.foldl (init := ({} : Std.HashSet String))
      fun set declaration => (get declaration).foldl (init := set) Std.HashSet.insert
    collected.toArray.qsort (· < ·)
  let record : Journal.CheckRecord := {
    checkedAt := ← Journal.timestampNow
    path
    clean := report.isClean
    declarations := report.declarations.size
    reuses := union (·.dependencies)
    axioms := union (·.axioms.map Name.toString)
    errors := report.fatal ++ report.declarations.flatMap (·.errors)
    diagnostics := report.diagnostics
  }
  let updated : Journal.Item := {
    item with
    draft? := some path
    attempts := item.attempts + 1
    stage := stageAfterCheck item.stage report.isClean
    lastCheck? := some record
    updated := record.checkedAt
  }
  Journal.save context.workRoot context.workPublish? updated
  return updated

end Frontier.CLI
