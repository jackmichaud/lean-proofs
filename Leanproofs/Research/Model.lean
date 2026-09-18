/-
Copyright (c) 2026 Jack Michaud. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Michaud
-/

import Lean

/-!
# Research event model

An append-only, explicitly untrusted account of research activity. Events describe what an
actor tried and what a tool reported; they are never mathematical evidence. Only separately
audited Lean declarations may cross Frontier's trust boundary.
-/

namespace Frontier.Research

structure AttemptId where value : String deriving BEq, DecidableEq, Hashable, Inhabited, Repr
structure ProofStateId where value : String deriving BEq, DecidableEq, Hashable, Inhabited, Repr
structure TransitionId where value : String deriving BEq, DecidableEq, Hashable, Inhabited, Repr
structure RetrievalId where value : String deriving BEq, DecidableEq, Hashable, Inhabited, Repr
structure RunId where value : String deriving BEq, DecidableEq, Hashable, Inhabited, Repr
structure EventId where value : String deriving BEq, DecidableEq, Hashable, Inhabited, Repr

/-- Stable IDs are deliberately narrower than filenames. Storage validates them again before
using an attempt ID as a path component. -/
def isValidIdValue (value : String) : Bool :=
  !value.isEmpty && value.all fun c =>
    c.toNat < 128 && (c.isAlphanum || c == '-' || c == '_')

def validateIdValue (kind value : String) : Except String String := do
  unless isValidIdValue value do
    throw s!"invalid {kind} '{value}'; expected ASCII letters, digits, '-' or '_'"
  return value

def AttemptId.parse (value : String) : Except String AttemptId :=
  return ⟨← validateIdValue "attempt id" value⟩
def ProofStateId.parse (value : String) : Except String ProofStateId :=
  return ⟨← validateIdValue "proof state id" value⟩
def TransitionId.parse (value : String) : Except String TransitionId :=
  return ⟨← validateIdValue "transition id" value⟩
def RetrievalId.parse (value : String) : Except String RetrievalId :=
  return ⟨← validateIdValue "retrieval id" value⟩
def RunId.parse (value : String) : Except String RunId :=
  return ⟨← validateIdValue "run id" value⟩
def EventId.parse (value : String) : Except String EventId :=
  return ⟨← validateIdValue "event id" value⟩

/-- Identity of the exact environment in which an observation was made. -/
structure EnvironmentFingerprint where
  leanVersion : String
  mathlibRevision : String
  frontierRevision : String
  importsHash : String
  policyVersion : String
  deriving BEq, Inhabited, Repr

inductive ActorKind where
  | human | agent | tool | system
  deriving BEq, DecidableEq, Inhabited, Repr

/-- Provenance is descriptive and untrusted. `runId` connects events emitted by one invocation;
`model` and `configuration` make agent behavior reproducible where possible. -/
structure Actor where
  kind : ActorKind
  name : String
  runId : RunId
  model? : Option String := none
  configuration? : Option String := none
  deriving BEq, Inhabited, Repr

structure AttemptCreated where
  title : String
  goal : String
  initialStateId? : Option ProofStateId := none
  parentAttemptId? : Option AttemptId := none
  deriving BEq, Inhabited, Repr

structure RetrievalPerformed where
  retrievalId : RetrievalId
  query : String
  results : Array String := #[]
  deriving BEq, Inhabited, Repr

structure ActionProposed where
  stateId : ProofStateId
  action : String
  retrievalIds : Array RetrievalId := #[]
  deriving BEq, Inhabited, Repr

inductive EvaluationOutcome where
  | accepted | rejected | timedOut | resourceExhausted
  deriving BEq, DecidableEq, Inhabited, Repr

structure ActionEvaluated where
  transitionId : TransitionId
  parentStateId : ProofStateId
  childStateId? : Option ProofStateId := none
  action : String
  outcome : EvaluationOutcome
  goals : Array String := #[]
  diagnostics : Array String := #[]
  usedDeclarations : Array String := #[]
  complete : Bool := false
  wallMs? : Option Nat := none
  heartbeats? : Option Nat := none
  deriving BEq, Inhabited, Repr

structure BranchSelected where
  stateId : ProofStateId
  reason? : Option String := none
  deriving BEq, Inhabited, Repr

structure BranchAbandoned where
  stateId : ProofStateId
  reason : String
  deriving BEq, Inhabited, Repr

structure ArtifactChecked where
  artifact : String
  clean : Bool
  declarations : Nat := 0
  errors : Array String := #[]
  diagnostics : Array String := #[]
  deriving BEq, Inhabited, Repr

structure PolicyRejected where
  artifact : String
  violations : Array String
  deriving BEq, Inhabited, Repr

structure ArtifactPromoted where
  artifact : String
  catalogId : String
  deriving BEq, Inhabited, Repr

inductive Payload where
  | attemptCreated (value : AttemptCreated)
  | retrievalPerformed (value : RetrievalPerformed)
  | actionProposed (value : ActionProposed)
  | actionEvaluated (value : ActionEvaluated)
  | branchSelected (value : BranchSelected)
  | branchAbandoned (value : BranchAbandoned)
  | artifactChecked (value : ArtifactChecked)
  | policyRejected (value : PolicyRejected)
  | artifactPromoted (value : ArtifactPromoted)
  deriving BEq, Inhabited, Repr

def Payload.kind : Payload → String
  | .attemptCreated _ => "attempt.created"
  | .retrievalPerformed _ => "retrieval.performed"
  | .actionProposed _ => "action.proposed"
  | .actionEvaluated _ => "action.evaluated"
  | .branchSelected _ => "branch.selected"
  | .branchAbandoned _ => "branch.abandoned"
  | .artifactChecked _ => "artifact.checked"
  | .policyRejected _ => "policy.rejected"
  | .artifactPromoted _ => "artifact.promoted"

/-- Sequence numbers begin at one and are contiguous within one attempt stream. -/
structure Event where
  schemaVersion : Nat := 1
  eventId : EventId
  attemptId : AttemptId
  sequence : Nat
  occurredAt : String
  environment : EnvironmentFingerprint
  actor : Actor
  payload : Payload
  deriving BEq, Inhabited, Repr

/-- This constant is exported with views and serialized events so consumers cannot mistake
research history for verified mathematical evidence. -/
def trustNotice : String :=
  "Untrusted research history. Events record activity and are not mathematical evidence."

end Frontier.Research
