/-
Copyright (c) 2026 Jack Michaud. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Michaud
-/

import Leanproofs.Research.Storage

namespace Frontier.Research

/-- Materialized work-item view. Its append-only source remains authoritative and untrusted. -/
structure AttemptSummary where
  trusted : Bool := false
  trustNotice : String := Frontier.Research.trustNotice
  attemptId : AttemptId
  parentAttemptId? : Option AttemptId := none
  title : String := ""
  goal : String := ""
  draftPath? : Option String := none
  note? : Option String := none
  stage : Stage := .exploring
  eventCount : Nat := 0
  proposedActions : Nat := 0
  evaluatedActions : Nat := 0
  retrievals : Nat := 0
  selectedBranches : Nat := 0
  abandonedBranches : Nat := 0
  artifactChecks : Nat := 0
  lastCheck? : Option ArtifactChecked := none
  lastCheckAt? : Option String := none
  policyRejections : Nat := 0
  promotedArtifact? : Option String := none
  promotedCatalogId? : Option String := none
  createdAt : String := ""
  updatedAt : String := ""
  deriving BEq, Inhabited, Repr

/-- One accepted transition needed to reconstruct a recorded proof state. -/
structure ReplayTransition where
  parentStateId : ProofStateId
  childStateId : ProofStateId
  action : String
  goals : Array String := #[]
  complete : Bool := false
  deriving BEq, Inhabited, Repr

/-- A pure recipe for rebuilding a proof state in a fresh Lean process. -/
structure ReplayPlan where
  proposition : String
  initialStateId : ProofStateId
  targetStateId : ProofStateId
  transitions : Array ReplayTransition := #[]
  deriving BEq, Inhabited, Repr

private def lineageError (message : String) : Except String α :=
  .error s!"malformed replay lineage: {message}"

/-- Recover the unique accepted-action path from an attempt's initial state to `targetStateId`.
The recorded child IDs are labels for checking replay results; they are not live Lean state IDs. -/
def replayPlan (attemptId : AttemptId) (events : Array Event)
    (targetStateId : ProofStateId) : Except String ReplayPlan := do
  match validateStream attemptId events with
  | .error message => lineageError message
  | .ok _ => pure ()
  let some first := events[0]? | return ← lineageError "attempt stream is empty"
  let (.attemptCreated created) := first.payload |
    return ← lineageError "attempt stream does not begin with attempt.created"
  let some proposition := created.proposition? |
    throw "cannot build a replay plan: attempt has no proposition"
  let some initialStateId := created.initialStateId? |
    return ← lineageError "attempt proposition has no initial state"
  let mut current := targetStateId
  let mut reversed : Array ReplayTransition := #[]
  let mut visited : Std.HashSet ProofStateId := {}
  while current != initialStateId do
    if visited.contains current then
      return ← lineageError s!"cycle at proof state '{current.value}'"
    visited := visited.insert current
    let parents := events.filterMap fun event => match event.payload with
      | .actionEvaluated value =>
          if value.outcome == .accepted && value.childStateId? == some current then some value else none
      | _ => none
    if parents.size == 0 then
      throw s!"unknown or unreachable proof state '{targetStateId.value}'"
    unless parents.size == 1 do
      return ← lineageError s!"proof state '{current.value}' has multiple accepted parents"
    let transition := parents[0]!
    reversed := reversed.push {
      parentStateId := transition.parentStateId
      childStateId := current
      action := transition.action
      goals := transition.goals
      complete := transition.complete }
    current := transition.parentStateId
  let transitions := reversed.reverse
  for index in [:transitions.size] do
    if transitions[index]!.complete && index + 1 < transitions.size then
      return ← lineageError s!"completed proof state '{transitions[index]!.childStateId.value}' has descendants"
  return { proposition, initialStateId, targetStateId, transitions }

private def initialStage (metadata : WorkMetadata) : Stage :=
  if metadata.draftPath?.isSome then .drafting else .exploring

private def stageAfterCheck (current : Stage) (clean : Bool) : Stage :=
  if current == .registered || current == .abandoned then current
  else if clean then .clean else .drafting

def materialize (attemptId : AttemptId) (events : Array Event) : Except String AttemptSummary := do
  validateStream attemptId events
  let mut summary : AttemptSummary := { attemptId }
  for event in events do
    summary := { summary with eventCount := summary.eventCount + 1, updatedAt := event.occurredAt }
    match event.payload with
    | .attemptCreated value => summary := { summary with
        parentAttemptId? := value.parentAttemptId?
        title := value.metadata.title
        goal := value.metadata.goal
        draftPath? := value.metadata.draftPath?
        note? := value.metadata.note?
        stage := initialStage value.metadata
        createdAt := event.occurredAt }
    | .metadataUpdated value => summary := { summary with
        title := value.metadata.title
        goal := value.metadata.goal
        draftPath? := value.metadata.draftPath?
        note? := value.metadata.note? }
    | .stageChanged value => summary := { summary with stage := value.toStage }
    | .retrievalPerformed _ => summary := { summary with retrievals := summary.retrievals + 1 }
    | .actionProposed _ => summary := { summary with proposedActions := summary.proposedActions + 1 }
    | .actionEvaluated _ => summary := { summary with evaluatedActions := summary.evaluatedActions + 1 }
    | .branchSelected _ => summary := { summary with selectedBranches := summary.selectedBranches + 1 }
    | .branchAbandoned _ => summary := { summary with abandonedBranches := summary.abandonedBranches + 1 }
    | .artifactChecked value => summary := { summary with
        draftPath? := some value.artifact
        stage := stageAfterCheck summary.stage value.clean
        artifactChecks := summary.artifactChecks + 1
        lastCheck? := some value
        lastCheckAt? := some event.occurredAt }
    | .policyRejected _ => summary := { summary with policyRejections := summary.policyRejections + 1 }
    | .artifactPromoted value => summary := { summary with
        stage := .registered
        promotedArtifact? := some value.artifact
        promotedCatalogId? := some value.catalogId }
  return summary

def readSummary (root : System.FilePath) (attemptId : AttemptId) : IO (Except String AttemptSummary) := do
  match ← readEvents root attemptId with
  | .error message => return .error message
  | .ok events => return materialize attemptId events

def listSummaries (root : System.FilePath) : IO (Except String (Array AttemptSummary)) := do
  let ids ← match ← listAttemptIds root with
    | .ok ids => pure ids
    | .error message => return .error message
  let mut summaries := #[]
  for id in ids do
    match ← readSummary root id with
    | .ok summary => summaries := summaries.push summary
    | .error message => return .error message
  return .ok summaries

end Frontier.Research
