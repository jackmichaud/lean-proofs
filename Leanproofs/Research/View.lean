/-
Copyright (c) 2026 Jack Michaud. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Michaud
-/

import Leanproofs.Research.Storage

namespace Frontier.Research

/-- A lossy materialized view. The event stream remains authoritative and untrusted. This
contains the counter and latest check needed to replace the corresponding journal fields. -/
structure AttemptSummary where
  trusted : Bool := false
  trustNotice : String := Frontier.Research.trustNotice
  attemptId : AttemptId
  title : String := ""
  goal : String := ""
  eventCount : Nat := 0
  proposedActions : Nat := 0
  evaluatedActions : Nat := 0
  retrievals : Nat := 0
  selectedBranches : Nat := 0
  abandonedBranches : Nat := 0
  /-- Number of artifact checks, corresponding to the legacy journal's `attempts` count. -/
  artifactChecks : Nat := 0
  lastCheck? : Option ArtifactChecked := none
  lastCheckAt? : Option String := none
  policyRejections : Nat := 0
  promotedCatalogId? : Option String := none
  updatedAt : String := ""
  deriving BEq, Inhabited, Repr

def materialize (attemptId : AttemptId) (events : Array Event) : Except String AttemptSummary := do
  validateStream attemptId events
  let mut summary : AttemptSummary := { attemptId }
  for event in events do
    summary := { summary with eventCount := summary.eventCount + 1, updatedAt := event.occurredAt }
    match event.payload with
    | .attemptCreated value => summary := { summary with title := value.title, goal := value.goal }
    | .retrievalPerformed _ => summary := { summary with retrievals := summary.retrievals + 1 }
    | .actionProposed _ => summary := { summary with proposedActions := summary.proposedActions + 1 }
    | .actionEvaluated _ => summary := { summary with evaluatedActions := summary.evaluatedActions + 1 }
    | .branchSelected _ => summary := { summary with selectedBranches := summary.selectedBranches + 1 }
    | .branchAbandoned _ => summary := { summary with abandonedBranches := summary.abandonedBranches + 1 }
    | .artifactChecked value =>
        summary := { summary with
          artifactChecks := summary.artifactChecks + 1
          lastCheck? := some value
          lastCheckAt? := some event.occurredAt }
    | .policyRejected _ => summary := { summary with policyRejections := summary.policyRejections + 1 }
    | .artifactPromoted value =>
        summary := { summary with promotedCatalogId? := some value.catalogId }
  return summary

def readSummary (root : System.FilePath) (attemptId : AttemptId) : IO (Except String AttemptSummary) := do
  match ← readEvents root attemptId with
  | .error message => return .error message
  | .ok events => return materialize attemptId events

end Frontier.Research
