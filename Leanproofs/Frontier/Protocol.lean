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
          | "remove" =>
              match rest with
              | [id] => workRemove context id
              | _ => return .failure "work remove expects exactly one item id"
          | "export" =>
              match rest with
              | [] => workExport context Journal.defaultExportPath
              | [path] => workExport context path
              | _ => return .failure "work export expects at most one path"
          | _ =>
              return .failure s!"unknown work subcommand '{subcommand}'; \
                expected list, add, show, set, remove, or export"
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

/-! ## Serve

Importing mathlib with `loadExts := true` costs roughly twenty seconds, and every one-shot
command pays it in full. An agent ranking premises or iterating on a draft makes many calls, so
the environment has to outlive a single command or the tool is unusable for its main purpose.

`frontier serve` imports once and then answers requests on stdin: one request per line, one
JSON response per line. The protocol is newline-delimited JSON rather than anything richer
precisely so that a caller can speak it from a pipe with no client library.

## This is a local tool, not a service

A session speaks a request protocol and holds state, which makes it look like something to put
behind a socket. It is not. `serve` exposes `check`, which elaborates a Lean file in this
process — and elaboration runs arbitrary code, so anything that can hand a path to a session
can run code as whoever started it. Reachability is the only difference between that and
`frontier check`, and reachability is the whole risk.

Exposing this beyond the local process needs the sandbox described in
`docs/retrieval-and-agents.md`: process isolation, resource limits, a syntactic prescreen, and
the axiom policy at the gate. Until then, one session per agent, on the agent's own machine.
-/

/-- Parse one request line.

A JSON array is the real protocol. A bare command line is also accepted so a human can drive a
session by hand, but it splits on spaces and therefore cannot carry a quoted `--goal`; that is
what the array form is for. -/
def parseRequest (line : String) : Except String (List String) :=
  let trimmed := line.trimAscii.toString
  if trimmed.startsWith "[" then
    match Json.parse trimmed with
    | .error message => .error s!"invalid JSON request: {message}"
    | .ok json =>
        match json.getArr? with
        | .error message => .error s!"a JSON request must be an array of arguments: {message}"
        | .ok values =>
            match values.mapM Json.getStr? with
            | .error message => .error s!"every argument must be a string: {message}"
            | .ok args => .ok args.toList
  else
    .ok ((trimmed.splitOn " ").filter (!·.isEmpty))

/-- Execute one typed request. The typed layer is deliberately a small allowlist: adding an
operation requires an explicit branch, so a typo or future operation can never look like a
successful empty command. -/
def computeTyped (context : Context) (request : API.Request) : IO Json := do
  match API.validateRequest context request with
  | .error error =>
      return API.failureResponse context (some request.requestId) (some request.operation) error
  | .ok () =>
      match request.operation with
      | "capabilities.get" =>
          return API.successResponse context request API.capabilitiesJson
      | "environment.describe" =>
          return API.successResponse context request (API.environmentJson context)
      | "cli.execute" =>
          match API.cliArgs request with
          | .error error =>
              return API.failureResponse context (some request.requestId)
                (some request.operation) error
          | .ok args =>
              let payload ← try compute context args
                catch exception =>
                  return API.failureResponse context (some request.requestId)
                    (some request.operation) {
                      code := .internalError
                      message := exception.toString
                    }
              if payload.exitCode == 0 then
                return API.successResponse context request (Json.mkObj [
                  ("command", toJson (args.headD "")),
                  ("exitCode", toJson payload.exitCode.toNat),
                  ("result", payload.toJson)
                ])
              else
                let message := match payload with
                  | .failure message => message
                  | _ => s!"command '{args.headD ""}' returned a nonzero exit code"
                return API.responseJson (some request.requestId) (some request.operation)
                  (API.environmentId context) (some (Json.mkObj [
                    ("command", toJson (args.headD "")),
                    ("exitCode", toJson payload.exitCode.toNat),
                    ("result", payload.toJson)
                  ])) (some { code := .commandFailed, message })
      | operation =>
          return API.failureResponse context (some request.requestId) (some operation) {
            code := .unsupportedOperation
            message := s!"unsupported operation '{operation}'"
          }

partial def serveLoop (context : Context) (stdin stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return ()                       -- EOF ends the session
  let request := line.trimAscii.toString
  if request == "quit" || request == "exit" then return ()
  unless request.isEmpty do
    let response ←
      if request.startsWith "{" then
        match API.parseRequest request with
        | .error error =>
            let (requestId?, operation?) := API.requestMetadata request
            pure (API.failureResponse context requestId? operation? error)
        | .ok typed =>
            -- A malformed request must not end a session an agent is minutes into.
            try computeTyped context typed
            catch exception =>
              pure (API.failureResponse context (some typed.requestId) (some typed.operation) {
                code := .internalError
                message := exception.toString
              })
      else
        let (command, payload) ←
          match parseRequest request with
          | .error message => pure ("", Payload.failure message)
          | .ok args => do
              let payload ← try compute context args
                catch exception => pure (Payload.failure exception.toString)
              pure (args.headD "", payload)
        pure <| Json.mkObj [
          ("command", toJson command),
          ("ok", toJson (payload.exitCode == 0)),
          ("exitCode", toJson payload.exitCode.toNat),
          ("result", payload.toJson)
        ]
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
    ("schemaVersion", toJson (2 : Nat)),
    ("entries", toJson context.catalog.size),
    ("workRoot", toJson context.workRoot.toString),
    ("usage", toJson usageLines)
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
