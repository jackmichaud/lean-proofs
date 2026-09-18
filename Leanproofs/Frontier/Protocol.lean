/-
Copyright (c) 2026 Jack Michaud. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Michaud
-/

import Leanproofs.Frontier.Work
import Leanproofs.Frontier.API

open Lean

namespace Frontier.CLI

/-! ### Dispatch -/

def exportTo (context : Context) (path : System.FilePath) : IO Payload := do
  let (audits, globalErrors) ← auditCatalog context
  let json := catalogJson audits globalErrors
  if let some parent := path.parent then
    IO.FS.createDirAll parent
  IO.FS.writeFile path (json.pretty 120)
  return .exported {
    path := path.toString
    entries := audits.size
    valid := globalErrors.isEmpty && audits.all Audit.isValid
  }

/-- Premise ranking for a registered entry.

Excludes the entry's own declarations *and* every entry that transitively depends on it: those
are the candidates guaranteed to be useless, since building the goal's proof on them would be
circular. -/
def suggestForEntry (context : Context) (entry : Entry) (limit : Nat) : IO Payload := do
  let some statementInfo := context.find? entry.statement
    | return .failure s!"statement declaration '{entry.statement}' does not exist"
  -- The denoted proposition, not the declaration type: for a `def _ : Prop` the type is just
  -- `Prop` and shares no constants with anything, which silently returns no candidates.
  let some proposition := statementExpr? statementInfo
    | return .failure s!"statement declaration '{entry.statement}' does not denote a proposition"
  let (audits, _) ← auditCatalog context
  let excluded := registeredDeclarations context.catalog (dependentClosure audits entry.id)
  let candidates ← rankPremises context proposition excluded limit
  return .suggest entry.title (← prettyExpr context.env proposition) candidates

/-- Run one command against an already-imported environment. -/
def compute (context : Context) (args : List String) : IO Payload := do
  match args with
  | [] => return .help
  | command :: rest =>
    match command with
    | "help" | "--help" | "-h" => return .help
    | "policy" => return .policy
    | "validate" =>
        let (audits, globalErrors) ← auditCatalog context
        return .validate audits globalErrors
    | "list" =>
        let (audits, _) ← auditCatalog context
        if rest.isEmpty then
          return .list audits
        let query := (" ".intercalate rest).toLower
        return .list <| audits.filter fun audit =>
          let tags := " ".intercalate audit.entry.tags.toList
          containsSubstring
            s!"{audit.entry.id} {audit.entry.title} {audit.entry.topic} {tags}".toLower query
    | "show" =>
        match rest with
        | [id] =>
            match context.entry? id with
            | none => return .failure s!"unknown registry id '{id}'"
            | some entry =>
                let (audit, _) ← (auditEntry context entry).run {}
                return .inspect audit
        | _ => return .failure "show expects exactly one registry id"
    | "check" =>
        match takeNat "--heartbeats" defaultDraftHeartbeats rest with
        | .error message => return .failure message
        | .ok (heartbeats, rest) =>
        match takeString "--work" rest with
        | .error message => return .failure message
        | .ok (work?, rest) =>
            -- Unbounded elaboration is fine for a one-shot command that only its caller is
            -- waiting on. Inside a session it is not: one non-terminating request blocks every
            -- later one, and the caller cannot tell a hang from slow work.
            if context.session && heartbeats == 0 then
              return .failure "--heartbeats 0 disables the elaboration limit, which would hang \
                this serve session for every later request; pass a positive budget"
            match rest with
            | [path] =>
                let item? : Except Payload (Option Journal.Item) ←
                  match work? with
                  | none => pure (.ok none)
                  | some id =>
                      match ← loadItem context id with
                      | .error payload => pure (.error payload)
                      | .ok item => pure (.ok (some item))
                match item? with
                | .error payload => return payload
                | .ok item? =>
                    let report ← checkDraft context path heartbeats
                    match item? with
                    | none => return .draft path report none none
                    | some item =>
                        -- A fatal report means elaboration never meaningfully ran — the file
                        -- was missing, or it imports something absent from the environment.
                        -- Recording that as an attempt would bump the counter, overwrite
                        -- `draft?` with a path that may not even exist, and demote a
                        -- previously `clean` item, all on the strength of a caller error
                        -- rather than anything about the mathematics.
                        if report.fatal.isEmpty then
                          return .draft path report (some item.id)
                            (some (← recordCheck context item path report))
                        else
                          return .draft path report (some item.id) none
            | _ => return .failure "check expects exactly one path to a Lean file"
    | "work" =>
        match rest with
        | [] => workList context none
        | subcommand :: rest =>
          match subcommand with
          | "list" =>
              match takeString "--stage" rest with
              | .error message => return .failure message
              | .ok (stage?, rest) =>
                  if rest.isEmpty then workList context stage?
                  else return .failure "work list takes only --stage"
          | "add" =>
              match takeString "--goal" rest with
              | .error message => return .failure message
              | .ok (goal?, rest) =>
              match takeString "--draft" rest with
              | .error message => return .failure message
              | .ok (draft?, rest) =>
              match takeString "--note" rest with
              | .error message => return .failure message
              | .ok (note?, rest) =>
                  if rest.isEmpty then
                    return .failure "work add expects a title"
                  else
                    workAdd context (" ".intercalate rest) goal? draft? note?
          | "show" =>
              match rest with
              | [id] => workShow context id
              | _ => return .failure "work show expects exactly one item id"
          | "set" =>
              match takeString "--stage" rest with
              | .error message => return .failure message
              | .ok (stage?, rest) =>
              match takeString "--goal" rest with
              | .error message => return .failure message
              | .ok (goal?, rest) =>
              match takeString "--draft" rest with
              | .error message => return .failure message
              | .ok (draft?, rest) =>
              match takeString "--note" rest with
              | .error message => return .failure message
              | .ok (note?, rest) =>
              match takeString "--entry" rest with
              | .error message => return .failure message
              | .ok (entry?, rest) =>
                  match rest with
                  | [id] =>
                      if stage?.isNone && goal?.isNone && draft?.isNone
                          && note?.isNone && entry?.isNone then
                        return .failure "work set needs at least one of \
                          --stage, --goal, --draft, --note, --entry"
                      workSet context id stage? goal? draft? note? entry?
                  | _ => return .failure "work set expects exactly one item id"
          | "abandon" =>
              match takeString "--reason" rest with
              | .error message => return .failure message
              | .ok (some reason, [id]) => workAbandon context id reason
              | .ok (none, _) =>
                  return .failure "work abandon requires --reason '<reason>'"
              | .ok (_, _) =>
                  return .failure "work abandon expects exactly one item id"
          | "export" =>
              match rest with
              | [] => workExport context Journal.defaultExportPath
              | [path] => workExport context path
              | _ => return .failure "work export expects at most one path"
          | _ =>
              return .failure s!"unknown work subcommand '{subcommand}'; \
                expected list, add, show, set, abandon, or export"
    | "search" =>
        let (definitions, rest) := takeFlag "--definitions" rest
        match takeNat "--limit" defaultSearchLimit rest with
        | .error message => return .failure message
        | .ok (limit, rest) =>
            let query := " ".intercalate rest
            if query.trimAscii.isEmpty then
              return .failure "search requires a non-empty query"
            let (hits, total) ← searchDeclarations context query limit definitions
            return .search query hits total
    | "suggest" =>
        match takeString "--goal" rest with
        | .error _ =>
            return .failure "--goal expects a Lean proposition, for example \
              `suggest --goal '∀ n : ℕ, n + 0 = n'`"
        | .ok (goal?, rest) =>
        match takeNat "--limit" defaultSuggestLimit rest with
        | .error message => return .failure message
        | .ok (limit, rest) =>
            match goal?, rest with
            | some goal, [] =>
                match ← elabProposition context.env goal with
                | .error message => return .failure message
                | .ok proposition =>
                    -- A goal that is not in the catalog has no dependents, so there is nothing
                    -- circular to exclude.
                    let candidates ← rankPremises context proposition {} limit
                    return .suggest "goal" (← prettyExpr context.env proposition) candidates
            | some _, _ =>
                return .failure "suggest takes either --goal or a registry id, not both"
            | none, [id] =>
                match context.entry? id with
                | none => return .failure s!"unknown registry id '{id}'"
                | some entry => suggestForEntry context entry limit
            | none, _ =>
                return .failure "suggest expects a registry id or --goal '<proposition>'"
    | "prove" =>
        match takeNat "--heartbeats" defaultTacticHeartbeats rest with
        | .error message => return .failure message
        | .ok (heartbeats, rest) =>
        match takeString "--goal" rest with
        | .error message => return .failure message
        | .ok (goal?, rest) =>
        match takeString "--state" rest with
        | .error message => return .failure message
        | .ok (state?, rest) =>
        match takeString "--tactic" rest with
        | .error message => return .failure message
        | .ok (tactic?, rest) =>
            unless rest.isEmpty do
              return .failure s!"prove takes only --goal, --state, --tactic and \
                --heartbeats; did not expect '{" ".intercalate rest}'"
            -- Same reason as `check`: one unbounded tactic would hang every later request in
            -- the session behind it, and the caller cannot tell a hang from slow work.
            if context.session && heartbeats == 0 then
              return .failure "--heartbeats 0 disables the elaboration limit, which would hang \
                this serve session for every later request; pass a positive budget"
            match goal?, state? with
            | some _, some _ =>
                return .failure "prove takes either --goal to open an attempt or --state to \
                  continue one, not both"
            | none, none =>
                return .failure "prove expects --goal '<proposition>' to open an attempt, or \
                  --state <id> to continue one"
            | some goal, none =>
                match ← runProofStep context (.proposition goal) tactic? heartbeats with
                | .error message => return .failure message
                | .ok step => return .proof step
            | none, some text =>
                let some id := text.toNat?
                  | return .failure s!"--state expects a proof state id, got '{text}'"
                match ← context.proofState? id with
                | .error message => return .failure message
                | .ok state =>
                    match ← runProofStep context (.resume state) tactic? heartbeats with
                    | .error message => return .failure message
                    | .ok step => return .proof step
    | "graph" =>
        let (audits, _) ← auditCatalog context
        return .graph audits
    | "export" =>
        match rest with
        | [] => exportTo context "build/frontier.json"
        | [path] => exportTo context path
        | _ => return .failure "export expects at most one path"
    | "serve" =>
        return .failure "serve is a top-level command and cannot be nested inside a session"
    | _ => return .failure s!"invalid command '{command}'"

/-- Render a payload in the requested format and hand back its exit code. -/
def emit (asJson : Bool) (payload : Payload) : IO UInt32 := do
  if asJson then IO.println payload.toJson.compress else payload.print
  return payload.exitCode

/-! ## Typed local agent protocol -/

private def actionOutcomeString : ProofActionOutcome → String
  | .accepted => "accepted"
  | .complete => "complete"
  | .rejected => "rejected"
  | .policyRejected => "policyRejected"
  | .failed => "failed"

private def proofStepJson (step : ProofStep) : Json := Json.mkObj [
  ("stateId", toJson step.id),
  ("goals", toJson step.goals),
  ("errors", toJson step.errors),
  ("axioms", toJson (step.axioms.map Name.toString)),
  ("policyErrors", toJson step.policyErrors),
  ("script", toJson step.script),
  ("complete", toJson step.isComplete)
]

private def actionResultJson (result : ProofActionResult) : Json :=
  let stepFields := match result.step? with
    | some step => proofStepJson step
    | none => Json.mkObj [
        ("stateId", .null), ("goals", toJson (#[] : Array String)),
        ("errors", toJson (result.error?.toArray)),
        ("axioms", toJson (#[] : Array String)),
        ("policyErrors", toJson (#[] : Array String)),
        ("script", toJson (#[] : Array String)), ("complete", toJson false)]
  Json.mergeObj (Json.mkObj [
    ("actionId", toJson result.actionId),
    ("outcome", toJson (actionOutcomeString result.outcome)),
    ("error", match result.error? with | some value => toJson value | none => .null)
  ]) stepFields

private def requestFailure (context : Context) (request : API.Request) (error : API.Error) : Json :=
  API.failureResponse context (some request.requestId) (some request.operation) error

private def invalidGoal (context : Context) (request : API.Request) (message : String) : Json :=
  requestFailure context request { code := .invalidGoal, message }

private def missingState (context : Context) (request : API.Request) (message : String) : Json :=
  requestFailure context request { code := .stateNotFound, message }

private def researchFailure (context : Context) (request : API.Request) (message : String) : Json :=
  requestFailure context request { code := .researchState, message }

private def researchStateId (id : Nat) : Research.ProofStateId :=
  ⟨s!"state-{id}"⟩

private def loadAttemptEvents (context : Context) (request : API.Request)
    (attemptId : Research.AttemptId) : IO (Except Json (Array Research.Event)) := do
  match ← Research.readEvents context.workRoot attemptId with
  | .error message => return .error (researchFailure context request message)
  | .ok events =>
      if events.isEmpty then
        return .error (researchFailure context request s!"no research attempt '{attemptId.value}'")
      return .ok events

private def ownsState (events : Array Research.Event) (id : Research.ProofStateId) : Bool :=
  events.any fun event =>
    match event.payload with
    | .attemptCreated value => value.initialStateId? == some id
    | .actionEvaluated value => value.childStateId? == some id
    | _ => false

private def evaluationOutcome : ProofActionOutcome → Research.EvaluationOutcome
  | .accepted | .complete => .accepted
  | .rejected | .policyRejected | .failed => .rejected

private def evaluationPayload (parentStateId : Research.ProofStateId)
    (heartbeats : Nat) (action : API.BatchAction) (result : ProofActionResult) : Research.Payload :=
  let childStateId? := match result.outcome, result.step? with
    | .accepted, some step | .complete, some step => some (researchStateId step.id)
    | _, _ => none
  let diagnostics := match result.step? with
    | some step => step.errors ++ step.policyErrors
    | none => result.error?.toArray
  .actionEvaluated {
    transitionId := action.transitionId
    parentStateId
    childStateId?
    action := action.tactic
    outcome := evaluationOutcome result.outcome
    goals := result.step?.map (·.goals) |>.getD #[]
    diagnostics
    complete := result.outcome == .complete
    heartbeats? := some heartbeats
  }

def computeTyped (context : Context) (request : API.Request) : IO Json := do
  match API.validateRequest context request with
  | .error error => return requestFailure context request error
  | .ok () =>
      match request.operation with
      | "capabilities.get" =>
          if let .error error := API.emptyParams request then return requestFailure context request error
          return API.successResponse context request API.capabilitiesJson
      | "environment.describe" =>
          if let .error error := API.emptyParams request then return requestFailure context request error
          return API.successResponse context request (API.environmentJson context)
      | "research.attempt.create" =>
          let attemptId ← match API.requireAttemptId request with
            | .ok value => pure value
            | .error error => return requestFailure context request error
          let params ← match API.attemptCreateParams request with
            | .ok value => pure value
            | .error error => return requestFailure context request error
          match ← Research.readEvents context.workRoot attemptId with
          | .error message => return researchFailure context request message
          | .ok events => unless events.isEmpty do
              return researchFailure context request s!"research attempt '{attemptId.value}' already exists"
          if let some parent := params.parentAttemptId? then
            match ← loadAttemptEvents context request parent with
            | .error response => return response
            | .ok _ => pure ()
          let initialStep? ← match params.proposition? with
            | none => pure none
            | some proposition =>
                match ← runProofStep context (.proposition proposition) none defaultTacticHeartbeats with
                | .error message => return invalidGoal context request message
                | .ok step => pure (some step)
          let payload : Research.Payload := .attemptCreated {
            metadata := {
              title := params.title
              goal := params.goal
              note? := params.note?
            }
            initialStateId? := initialStep?.map fun step => researchStateId step.id
            parentAttemptId? := params.parentAttemptId?
          }
          match ← appendResearch context attemptId.value request.actor #[payload] with
          | .error message => return researchFailure context request message
          | .ok _ =>
              return API.successResponse context request (Json.mkObj [
                ("attemptId", toJson attemptId.value),
                ("initialProofState", match initialStep? with
                  | some step => proofStepJson step
                  | none => .null)])
      | "declarations.search" =>
          match API.searchParams request with
          | .error error => return requestFailure context request error
          | .ok params =>
              let (hits, total) ← searchDeclarations context params.query params.limit
                params.includeDefinitions
              return API.successResponse context request (Json.mkObj [
                ("query", toJson params.query), ("total", toJson total),
                ("hits", Json.arr (hits.map searchHitJson))])
      | "premises.retrieve" =>
          let attemptId ← match API.requireAttemptId request with
            | .ok value => pure value
            | .error error => return requestFailure context request error
          let params ← match API.premiseParams request with
            | .ok value => pure value
            | .error error => return requestFailure context request error
          match ← loadAttemptEvents context request attemptId with
          | .error response => return response
          | .ok _ => pure ()
          match ← elabProposition context.env params.goal with
          | .error message => return invalidGoal context request message
          | .ok goal =>
              let candidates ← rankPremises context goal {} params.limit
              let payload : Research.Payload := .retrievalPerformed {
                retrievalId := params.retrievalId
                query := params.goal
                results := candidates.map (·.name.toString)
              }
              match ← appendResearch context attemptId.value request.actor #[payload] with
              | .error message => return researchFailure context request message
              | .ok _ =>
                  return API.successResponse context request (Json.mkObj [
                    ("attemptId", toJson attemptId.value),
                    ("retrievalId", toJson params.retrievalId.value),
                    ("goal", toJson params.goal),
                    ("proposition", toJson (← prettyExpr context.env goal)),
                    ("candidates", Json.arr (candidates.map premiseJson))])
      | "proof.evaluateBatch" =>
          let attemptId ← match API.requireAttemptId request with
            | .ok value => pure value
            | .error error => return requestFailure context request error
          let params ← match API.batchParams request with
            | .ok value => pure value
            | .error error => return requestFailure context request error
          let events ← match ← loadAttemptEvents context request attemptId with
            | .ok value => pure value
            | .error response => return response
          let parentStateId := researchStateId params.parentStateId
          unless ownsState events parentStateId do
            return researchFailure context request
              s!"proof state {params.parentStateId} does not belong to attempt '{attemptId.value}'"
          let state ← match ← context.proofState? params.parentStateId with
            | .ok value => pure value
            | .error message => return missingState context request message
          let actions := params.actions.map fun action =>
            ({ id := action.id, tactic := action.tactic } : ProofAction)
          let batch ← runProofBatch context (.resume state) actions params.heartbeats
          let mut payloads := #[]
          for (action, result) in params.actions.zip batch.results do
            payloads := payloads.push (.actionProposed {
              stateId := parentStateId
              action := action.tactic
              retrievalIds := action.retrievalIds
            })
            payloads := payloads.push (evaluationPayload parentStateId params.heartbeats action result)
            if result.outcome == .policyRejected then
              payloads := payloads.push (.policyRejected {
                artifact := s!"proof action {action.id}"
                violations := result.step?.map (·.policyErrors) |>.getD #["policy rejected"]
              })
          match ← appendResearch context attemptId.value request.actor payloads with
          | .error message => return researchFailure context request message
          | .ok _ =>
              return API.successResponse context request (Json.mkObj [
                ("attemptId", toJson attemptId.value),
                ("parentStateId", toJson params.parentStateId),
                ("results", Json.arr (batch.results.map actionResultJson))])
      | "proof.inspectState" =>
          let attemptId ← match API.requireAttemptId request with
            | .ok value => pure value
            | .error error => return requestFailure context request error
          let params ← match API.inspectParams request with
            | .ok value => pure value
            | .error error => return requestFailure context request error
          let events ← match ← loadAttemptEvents context request attemptId with
            | .ok value => pure value
            | .error response => return response
          unless ownsState events (researchStateId params.stateId) do
            return researchFailure context request
              s!"proof state {params.stateId} does not belong to attempt '{attemptId.value}'"
          match ← context.proofState? params.stateId with
          | .error message => return missingState context request message
          | .ok state =>
              match ← runProofStep context (.resume state) none params.heartbeats with
              | .error message => return invalidGoal context request message
              | .ok step =>
                  return API.successResponse context request (Json.mergeObj
                    (Json.mkObj [("requestedStateId", toJson params.stateId)])
                    (proofStepJson { step with id := params.stateId }))
      | operation =>
          return requestFailure context request {
            code := .unsupportedOperation
            message := s!"unsupported operation '{operation}'"
          }

/-- Parse and execute one request line. Invalid envelopes still preserve recoverable correlation
fields, and no malformed request terminates the warm session. -/
def handleRequest (context : Context) (source : String) : IO Json :=
  match API.parseRequest source with
  | .error error =>
      let (requestId?, operation?) := API.requestMetadata source
      pure (API.failureResponse context requestId? operation? error)
  | .ok request => try computeTyped context request catch exception =>
      pure (requestFailure context request { code := .internalError, message := exception.toString })

partial def serveLoop (context : Context) (stdin stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return ()                       -- EOF ends the session
  let request := line.trimAscii.toString
  unless request.isEmpty do
    let response ← handleRequest context request
    stdout.putStr (response.compress ++ "\n")
    stdout.flush
  serveLoop context stdin stdout

def runServe (context : Context) : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  -- `session := true` is what tightens the limits that only matter when later requests are
  -- waiting behind this one.
  let context := { context with session := true }
  let banner := Json.mkObj [
    ("ready", toJson true),
    ("project", toJson "Frontier"),
    ("apiVersion", toJson API.version),
    ("environment", toJson (API.environmentId context)),
    ("operations", API.capabilitiesJson)
  ]
  stdout.putStr (banner.compress ++ "\n")
  stdout.flush
  serveLoop context stdin stdout
  return 0

/-! ## Entry points -/

/-- Strip a global `--json` flag from anywhere in the argument list. -/
def takeJsonFlag (args : List String) : Bool × List String :=
  takeFlag "--json" args

/-- Commands that answer without importing the project environment, which costs several
seconds. -/
def runWithoutEnvironment? (args : List String) : Option (IO UInt32) :=
  let (asJson, rest) := takeJsonFlag args
  match rest with
  | [] | ["help"] | ["--help"] | ["-h"] => some (emit asJson .help)
  | ["policy"] => some (emit asJson .policy)
  | _ => none

def run (context : Context) (args : List String) : IO UInt32 := do
  let (asJson, rest) := takeJsonFlag args
  match rest with
  | "serve" :: _ => runServe context
  | _ => emit asJson (← compute context rest)

end Frontier.CLI
