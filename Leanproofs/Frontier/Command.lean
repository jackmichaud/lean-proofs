/-
Copyright (c) 2026 Jack Michaud. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Michaud
-/

import Leanproofs.Frontier.Proof
import Leanproofs.Frontier.Audit
import Leanproofs.Frontier.Retrieval

open Lean

namespace Frontier.CLI

/-! ## Export -/

def optionStringJson : Option String → Json
  | some value => toJson value
  | none => Json.null

def entryJson (audit : Audit) : Json :=
  Json.mkObj [
    ("id", toJson audit.entry.id),
    ("title", toJson audit.entry.title),
    ("summary", toJson audit.entry.summary),
    ("status", toJson audit.entry.status.toString),
    ("literature", toJson audit.entry.literature.toString),
    ("citation", optionStringJson audit.entry.citation?),
    ("topic", toJson audit.entry.topic),
    ("tags", toJson audit.entry.tags),
    ("statement", toJson audit.entry.statement.toString),
    ("statementType", toJson audit.statementType),
    ("statementAxioms", toJson audit.statementAxioms),
    ("declarationKind", toJson audit.declarationKind),
    ("certificate", optionStringJson (audit.entry.certificate?.map (·.declaration.toString))),
    ("certificateType", optionStringJson audit.certificateType?),
    ("evidence", optionStringJson
      (audit.entry.certificate?.map (·.method.toString))),
    ("baseTheory", optionStringJson audit.entry.baseTheory?),
    ("sanityChecks", Json.arr (audit.sanityChecks.map fun check =>
      Json.mkObj [("name", toJson check.name.toString), ("type", toJson check.type)])),
    ("dependencies", toJson audit.dependencies),
    ("axioms", toJson audit.axioms),
    ("authors", toJson audit.entry.claim.authors),
    ("tooling", toJson audit.entry.formalization.tooling),
    ("source", optionStringJson audit.entry.claim.source?),
    ("created", toJson audit.entry.claim.created),
    ("updated", toJson audit.entry.claim.updated),
    ("valid", toJson audit.isValid),
    ("errors", toJson audit.errors)
  ]

def catalogJson (audits : Array Audit) (globalErrors : Array String) : Json :=
  let count (predicate : Audit → Bool) : Nat :=
    audits.foldl (init := 0) fun total audit => if predicate audit then total + 1 else total
  Json.mkObj [
    ("schemaVersion", toJson (2 : Nat)),
    ("project", toJson "Frontier"),
    ("axiomPolicy", Json.mkObj [
      ("allowed", toJson (allowedAxioms.map Name.toString)),
      ("denied", toJson (deniedAxioms.map (·.1.toString)))
    ]),
    ("summary", Json.mkObj [
      ("total", toJson audits.size),
      ("valid", toJson (count Audit.isValid)),
      ("closed", toJson (count (·.entry.status.isClosed))),
      ("literatureUnresolved", toJson (count (·.entry.literature == .unresolved))),
      ("globalErrors", toJson globalErrors)
    ]),
    ("entries", Json.arr (audits.map entryJson))
  ]

/-! ## Commands

Every command computes a `Payload`, and every payload renders two ways: as text for a human at
a terminal, and as JSON for a program. One dispatch with two renderers — rather than a `--json`
branch threaded through each command — is what lets `frontier serve` expose the whole CLI over
a socket without a second implementation of anything.
-/

/-- Default elaboration budget for a draft, in heartbeats. Twice Lean's own default: drafts
run long tactics, and a generated proof that never terminates should fail rather than hang the
agent waiting on it. -/
def defaultDraftHeartbeats : Nat := 400000

structure ExportResult where
  path : String
  entries : Nat
  valid : Bool

/-- The result of one command, before it is rendered. -/
inductive Payload where
  | help
  | policy
  | validate (audits : Array Audit) (globalErrors : Array String)
  | list (audits : Array Audit)
  | inspect (audit : Audit)
  | search (query : String) (hits : Array SearchHit) (total : Nat)
  | suggest (target : String) (proposition : String) (candidates : Array PremiseCandidate)
  | graph (audits : Array Audit)
  /-- One step of an interactive proof attempt. -/
  | proof (step : ProofStep)
  /-- A draft report; the journal item `--work` named, if any; and the item as it stands after
  the report was folded in, if it was. A named item with no recorded result is a report that
  never elaborated — see the `check` dispatch. -/
  | draft (path : String) (report : DraftReport) (requested? : Option String)
      (recorded? : Option Journal.Item)
  | exported (result : ExportResult)
  /-- The journal board, plus any files that could not be read. -/
  | work (items : Array Journal.Item) (problems : Array String)
  /-- One journal item. `headline` says what just happened to it, and is empty for a plain
  `work show`. -/
  | workItem (item : Journal.Item) (headline : String)
  | workAbandoned (id : String)
  | failure (message : String)

def Payload.exitCode : Payload → UInt32
  | .validate audits globalErrors =>
      if globalErrors.isEmpty && audits.all Audit.isValid then 0 else 1
  | .draft _ report _ _ => if report.isClean then 0 else 1
  -- A tactic that ran and left goals is progress, not a failure; only a tactic that could not
  -- run, or a term that breaks the axiom policy, is a non-zero exit.
  | .proof step => if step.errors.isEmpty && step.policyErrors.isEmpty then 0 else 1
  | .exported result => if result.valid then 0 else 1
  -- A journal that cannot be fully read is a failure: silently listing the items that happened
  -- to parse would hide work from the board a human is relying on.
  | .work _ problems => if problems.isEmpty then 0 else 1
  | .failure _ => 1
  | _ => 0

def usageLines : Array String := #[
  "frontier validate",
  "frontier list [query]",
  "frontier show <registry id>",
  "frontier check <file.lean> [--heartbeats N] [--work <item id>]",
  "frontier search <name fragment> [--limit N] [--definitions]",
  "frontier suggest <registry id> [--limit N]",
  "frontier suggest --goal '<Lean proposition>' [--limit N]",
  "frontier prove --goal '<Lean proposition>' [--tactic '<tactics>'] [--heartbeats N]",
  "frontier prove --state <id> [--tactic '<tactics>'] [--heartbeats N]",
  "frontier work list [--stage <stage>]",
  "frontier work add <title> [--goal '<text>'] [--draft <file.lean>] [--note '<text>']",
  "frontier work show <item id>",
  "frontier work set <item id> [--stage <stage>] [--goal …] [--draft …] [--note …] [--entry …]",
  "frontier work abandon <item id> --reason '<reason>'",
  "frontier work export [path]",
  "frontier graph",
  "frontier policy",
  "frontier export [path]",
  "frontier serve"
]

def helpText : String :=
  let usage := "\n  ".intercalate (usageLines.map ("lake exe " ++ ·)).toList
  s!"Frontier: a Lean-checked mathematical research registry\n\n\
    Usage:\n  {usage}\n\n\
    Add --json to any command for machine-readable output.\n\n\
    `check` elaborates a draft Lean file against the compiled environment and reports Lean's\n\
    diagnostics, the axiom policy, and which catalog results the draft reuses. It does not\n\
    touch the registry, so it is the loop to iterate in. `--work <id>` records the report\n\
    against a journal item, which is how work survives the session that produced it.\n\n\
    `prove` is the loop below that: a proposition opens a proof state, `--tactic` advances it,\n\
    and the outstanding goals come back with their hypotheses. Each step returns a state id to\n\
    continue from, and a block that fails leaves the state it was tried against usable. Note\n\
    the two verdicts: a tactic reports an unknown identifier as a message and returns `sorry`,\n\
    so `closed` means only that no goals remain. `complete` is the one that means proved --\n\
    no goals, no errors, and a proof term inside the axiom policy.\n\n\
    `work` is a durable, untrusted append-only research history under work/. It is not a\n\
    submission endpoint: nothing there is executed, `clean` requires a passing `check --work`,\n\
    `registered` requires promotion to an existing catalog entry, and abandonment keeps the\n\
    complete event stream.\n\n\
    `serve` imports the environment once and then answers one request per line on stdin,\n\
    writing one JSON response per line. Importing mathlib costs about twenty seconds, so any\n\
    caller making more than a couple of requests should use it.\n\n\
    The default export path is build/frontier.json."

/-! ### JSON rendering -/

def searchHitJson (hit : SearchHit) : Json :=
  Json.mkObj [
    ("name", toJson hit.name.toString),
    ("kind", toJson hit.kind),
    ("type", toJson hit.type),
    ("catalogId", optionStringJson hit.catalogId?)
  ]

def premiseJson (candidate : PremiseCandidate) : Json :=
  Json.mkObj [
    ("score", scoreJson candidate.score),
    ("name", toJson candidate.name.toString),
    ("type", toJson candidate.type),
    ("catalogId", optionStringJson candidate.catalogId?)
  ]

/-- The summary view of an entry used by `list`. `show` and `export` emit the full record. -/
def listEntryJson (audit : Audit) : Json :=
  Json.mkObj [
    ("id", toJson audit.entry.id),
    ("title", toJson audit.entry.title),
    ("status", toJson audit.entry.status.toString),
    ("literature", toJson audit.entry.literature.toString),
    ("topic", toJson audit.entry.topic),
    ("tags", toJson audit.entry.tags),
    ("valid", toJson audit.isValid)
  ]

def draftDeclarationJson (declaration : DraftDeclaration) : Json :=
  Json.mkObj [
    ("name", toJson declaration.name.toString),
    ("kind", toJson declaration.kind),
    ("type", toJson declaration.type),
    ("axioms", toJson (declaration.axioms.map Name.toString)),
    ("dependencies", toJson declaration.dependencies),
    ("errors", toJson declaration.errors)
  ]

def graphJson (audits : Array Audit) : Json :=
  Json.mkObj [
    ("nodes", Json.arr (audits.map fun audit =>
      Json.mkObj [
        ("id", toJson audit.entry.id),
        ("title", toJson audit.entry.title),
        ("status", toJson audit.entry.status.toString),
        ("literature", toJson audit.entry.literature.toString)])),
    ("edges", Json.arr (audits.flatMap fun audit =>
      audit.dependencies.map fun dependency =>
        Json.mkObj [("from", toJson dependency), ("to", toJson audit.entry.id)]))
  ]

def policyJson : Json :=
  Json.mkObj [
    ("allowed", toJson (allowedAxioms.map Name.toString)),
    ("denied", Json.arr (deniedAxioms.map fun (name, reason) =>
      Json.mkObj [("axiom", toJson name.toString), ("reason", toJson reason)]))
  ]

def Payload.toJson : Payload → Json
  | .help => Json.mkObj [("usage", Lean.toJson usageLines)]
  | .policy => policyJson
  | .validate audits globalErrors => catalogJson audits globalErrors
  | .list audits => Json.mkObj [("entries", Json.arr (audits.map listEntryJson))]
  | .inspect audit => entryJson audit
  | .search query hits total =>
      Json.mkObj [
        ("query", Lean.toJson query),
        ("total", Lean.toJson total),
        ("shown", Lean.toJson hits.size),
        ("hits", Json.arr (hits.map searchHitJson))]
  | .suggest target proposition candidates =>
      Json.mkObj [
        ("target", Lean.toJson target),
        ("proposition", Lean.toJson proposition),
        ("candidates", Json.arr (candidates.map premiseJson))]
  | .graph audits => graphJson audits
  | .proof step =>
      Json.mkObj [
        ("state", Lean.toJson step.id),
        ("goals", Lean.toJson step.goals),
        ("goalCount", Lean.toJson step.goals.size),
        ("closed", Lean.toJson step.closed),
        -- `closed` and `complete` are both reported on purpose. They differ exactly when a
        -- tactic block closed the goal with something outside the axiom policy, and a caller
        -- reading only the first would call that a proof.
        ("complete", Lean.toJson step.isComplete),
        ("errors", Lean.toJson step.errors),
        ("axioms", Lean.toJson (step.axioms.map Name.toString)),
        ("policyErrors", Lean.toJson step.policyErrors),
        ("script", Lean.toJson step.script),
        ("scaffold", Lean.toJson step.scaffold)]
  | .draft path report requested? recorded? =>
      Json.mkObj [
        ("path", Lean.toJson path),
        ("clean", Lean.toJson report.isClean),
        ("fatal", Lean.toJson report.fatal),
        ("hasErrors", Lean.toJson report.hasErrors),
        ("diagnostics", Lean.toJson report.diagnostics),
        ("declarations", Json.arr (report.declarations.map draftDeclarationJson)),
        -- Both fields, so a caller can tell "no item was named" from "an item was named and
        -- deliberately left untouched" without inferring it from the fatal list.
        ("workItem", optionStringJson requested?),
        ("recorded", match recorded? with
          | some item => Journal.itemJson item
          | none => Json.null)]
  | .exported result =>
      Json.mkObj [
        ("path", Lean.toJson result.path),
        ("entries", Lean.toJson result.entries),
        ("valid", Lean.toJson result.valid)]
  | .work items problems =>
      Json.mkObj [
        -- Restated per response, not only in the published file: a caller reading this over
        -- `serve` should not have to consult the docs to learn the journal is not evidence.
        ("trusted", Lean.toJson false),
        ("counts", Json.mkObj (Journal.stages.toList.map fun stage =>
          (stage.toString, Lean.toJson
            (items.foldl (init := 0) fun total item =>
              if item.stage == stage then total + 1 else total : Nat)))),
        ("problems", Lean.toJson problems),
        ("items", Json.arr (items.map Journal.itemJson))]
  | .workItem item headline =>
      Json.mkObj [
        ("trusted", Lean.toJson false),
        ("headline", Lean.toJson headline),
        ("item", Journal.itemJson item)]
  | .workAbandoned id => Json.mkObj [("abandoned", Lean.toJson id)]
  | .failure message => Json.mkObj [("error", Lean.toJson message)]

/-! ### Text rendering -/

def printEntry (audit : Audit) : IO Unit := do
  IO.println s!"{audit.entry.title} [{audit.entry.status.toString}]"
  IO.println s!"id:           {audit.entry.id}"
  IO.println s!"topic:        {audit.entry.topic}"
  IO.println s!"literature:   {audit.entry.literature.toString}"
  if let some citation := audit.entry.citation? then
    IO.println s!"citation:     {citation}"
  IO.println s!"statement:    {audit.entry.statement}"
  IO.println s!"proposition:  {audit.statementType}"
  if let some certificate := audit.entry.certificate? then
    IO.println s!"certificate:  {certificate.declaration}"
    IO.println s!"evidence:     {certificate.method.toString}"
  if let some baseTheory := audit.entry.baseTheory? then
    IO.println s!"base theory:  {baseTheory}"
  IO.println s!"tags:         {", ".intercalate audit.entry.tags.toList}"
  let orNone (values : Array String) : String :=
    if values.isEmpty then "none" else ", ".intercalate values.toList
  IO.println s!"depends on:   {orNone audit.dependencies}"
  IO.println s!"axioms:       {orNone audit.axioms}"
  if !audit.sanityChecks.isEmpty then
    IO.println "sanity checks:"
    for check in audit.sanityChecks do
      IO.println s!"  {check.name} : {check.type}"
  IO.println s!"summary:      {audit.entry.summary}"
  if !audit.errors.isEmpty then
    for error in audit.errors do
      IO.eprintln s!"error: {error}"

def printDraft (path : String) (report : DraftReport) : IO Unit := do
  for failure in report.fatal do
    IO.eprintln s!"error: {failure}"
  for diagnostic in report.diagnostics do
    IO.print diagnostic
  if report.declarations.isEmpty then
    if report.fatal.isEmpty && !report.hasErrors then
      IO.println s!"{path}: no declarations. A draft has to name what it proves before \
        anything can be audited."
  else
    IO.println s!"\n{path}: {report.declarations.size} declaration(s)"
    for declaration in report.declarations do
      let marker := if declaration.errors.isEmpty then "ok " else "ERR"
      IO.println s!"{marker} {declaration.name} : {declaration.type}"
      if !declaration.axioms.isEmpty then
        IO.println s!"    axioms:  \
          {", ".intercalate (declaration.axioms.map Name.toString).toList}"
      if !declaration.dependencies.isEmpty then
        IO.println s!"    reuses:  {", ".intercalate declaration.dependencies.toList}"
      for error in declaration.errors do
        IO.eprintln s!"    {error}"
  if report.isClean then
    IO.println "\ndraft is clean: Lean accepted it and every declaration satisfies the axiom \
      policy.\nRegister it in Leanproofs/Catalog.lean to make it a catalog result \
      (see docs/adding-results.md)."
  else
    IO.println "\ndraft is not acceptable yet"

def printWorkItem (item : Journal.Item) : IO Unit := do
  IO.println s!"{item.title} [{item.stage.toString}]"
  IO.println s!"id:        {item.id}"
  if !item.goal.isEmpty then
    IO.println s!"goal:      {item.goal}"
  if let some draft := item.draft? then
    IO.println s!"draft:     {draft}"
  if let some entry := item.entry? then
    IO.println s!"entry:     {entry}"
  IO.println s!"attempts:  {item.attempts}"
  if let some note := item.note? then
    IO.println s!"note:      {note}"
  IO.println s!"created:   {item.created}"
  IO.println s!"updated:   {item.updated}"
  match item.lastCheck? with
  | none => IO.println "last check: never"
  | some record =>
      let verdict := if record.clean then "clean" else "not acceptable"
      IO.println s!"last check: {verdict} at {record.checkedAt} \
        ({record.declarations} declaration(s))"
      if !record.reuses.isEmpty then
        IO.println s!"  reuses:  {", ".intercalate record.reuses.toList}"
      if !record.axioms.isEmpty then
        IO.println s!"  axioms:  {", ".intercalate record.axioms.toList}"
      for error in record.errors do
        IO.println s!"  error:   {error}"
      for diagnostic in record.diagnostics do
        IO.println s!"  lean:    {diagnostic.trimAscii}"

def printProof (step : ProofStep) : IO Unit := do
  for error in step.errors do
    IO.eprintln s!"error: {error}"
  if step.goals.isEmpty then
    if step.errors.isEmpty then IO.println "No goals remain."
  else
    IO.println s!"{step.goals.size} goal(s):"
    for goal in step.goals do
      IO.println ""
      IO.println goal
  if !step.axioms.isEmpty then
    IO.println s!"\naxioms: {", ".intercalate (step.axioms.map Name.toString).toList}"
  for error in step.policyErrors do
    IO.eprintln s!"error: {error}"
  IO.println s!"\nstate {step.id}"
  if step.isComplete then
    -- Say what has and has not been established. The goal is closed and the term is within
    -- policy; it is still a tactic script in a session, not a registered result.
    IO.println "The goal is closed and the proof term satisfies the axiom policy. Save the \
      scaffold below to a file, `frontier check` it, then register it \
      (see docs/adding-results.md)."
    IO.println ""
    IO.println step.scaffold
  else if step.closed && step.errors.isEmpty then
    IO.println "No goals remain, but the proof term violates the axiom policy, so this is not \
      a proof. A tactic block reports an unknown identifier as a message and returns `sorry`, \
      which closes a goal without proving anything."

def Payload.print : Payload → IO Unit
  | .help => IO.println helpText
  | .policy => do
      IO.println "Frontier axiom policy\n"
      IO.println "allowed:"
      for name in allowedAxioms do
        IO.println s!"  {name}"
      IO.println "\ndenied:"
      for (name, reason) in deniedAxioms do
        IO.println s!"  {name}: {reason}"
      IO.println "\nAny other axiom reaching a statement, certificate, or sanity check is a \
        validation error."
  | .validate audits globalErrors => do
      let mut invalid := 0
      for audit in audits do
        if audit.isValid then
          IO.println s!"ok  {audit.entry.id} ({audit.entry.status.toString}, \
            literature: {audit.entry.literature.toString})"
        else
          invalid := invalid + 1
          IO.eprintln s!"ERR {audit.entry.id}"
          for error in audit.errors do
            IO.eprintln s!"    {error}"
      for error in globalErrors do
        IO.eprintln s!"ERR {error}"
      -- Count entries and catalog-wide errors separately. Folding the global errors into the
      -- entry tally reports a smaller number of passing entries than actually passed.
      IO.println s!"\n{audits.size - invalid}/{audits.size} registry entries passed"
      if !globalErrors.isEmpty then
        IO.println s!"{globalErrors.size} catalog-wide error(s)"
  | .list audits => do
      for audit in audits do
        IO.println s!"{audit.entry.id}\t{audit.entry.status.toString}\t\
          {audit.entry.literature.toString}\t{audit.entry.title}"
  | .inspect audit => printEntry audit
  | .search query hits total => do
      -- Branch on the total, not on the truncated page: `--limit 0` has matches but shows
      -- none of them, and reporting that as "nothing matched" is a different answer.
      if total == 0 then
        IO.println s!"No imported declarations matched '{query}'."
      else
        for hit in hits do
          IO.println s!"{hit.name} : {hit.type}"
        if total > hits.size then
          IO.println s!"\n… {total - hits.size} further matches not shown."
  | .suggest target proposition candidates => do
      IO.println s!"Reusable theorem candidates for {target}:"
      IO.println s!"  {proposition}\n"
      if candidates.isEmpty then
        IO.println "No candidates shared statement constants."
      else
        for candidate in candidates do
          let tag := match candidate.catalogId? with
            | some id => s!" (catalog: {id})"
            | none => ""
          IO.println s!"[{formatScore candidate.score}] {candidate.name}{tag} : {candidate.type}"
  | .proof step => printProof step
  | .graph audits => do
      IO.println "flowchart LR"
      for audit in audits do
        IO.println s!"  {audit.entry.id.replace "-" "_"}[\"{audit.entry.title}\"]"
      for audit in audits do
        for dependency in audit.dependencies do
          IO.println s!"  {dependency.replace "-" "_"} --> {audit.entry.id.replace "-" "_"}"
  | .draft path report requested? recorded? => do
      printDraft path report
      match recorded?, requested? with
      | some item, _ =>
          IO.println s!"recorded against work item '{item.id}' \
            (stage: {item.stage.toString}, attempt {item.attempts})"
      | none, some id =>
          -- Say it. An agent that asked for the attempt to be recorded and was silently given
          -- nothing would reasonably conclude the journal is broken.
          IO.println s!"work item '{id}' left unchanged: the draft was never elaborated, so \
            there is no attempt to record"
      | none, none => pure ()
  | .exported result => IO.println s!"Exported {result.entries} entries to {result.path}"
  | .work items problems => do
      if items.isEmpty && problems.isEmpty then
        IO.println "The work journal is empty. \
          `frontier work add \"<title>\"` starts an item."
      for item in items do
        let draft := item.draft?.getD "-"
        IO.println s!"{item.id}\t{item.stage.toString}\t{item.attempts}\t{draft}\t{item.title}"
      for problem in problems do
        IO.eprintln s!"ERR {problem}"
  | .workItem item headline => do
      unless headline.isEmpty do
        IO.println headline
      printWorkItem item
  | .workAbandoned id => IO.println s!"Abandoned work item '{id}'; history retained."
  | .failure message => do
      IO.eprintln s!"error: {message}"
      IO.eprintln "Run `lake exe frontier help` for usage."

/-! ### Argument parsing -/

/-- Strip a boolean flag from anywhere in the argument list. -/
def takeFlag (flag : String) (args : List String) : Bool × List String :=
  (args.contains flag, args.filter (· != flag))

/-- What looking for `--name value` found.

`absent` and `valueless` have to be different answers. Treating a trailing `--limit` as absent
leaves the flag in the positional arguments, where `search` folds it into the query and returns
zero hits with `ok: true` — a malformed request reported as a successful empty result, which is
the one failure mode that will send an agent off to rebuild something that already exists. -/
inductive OptionValue where
  | absent
  | valueless
  | value (text : String)
  deriving BEq, DecidableEq, Inhabited, Repr

/-- Read `--name value` out of the argument list, returning what was found and the remaining
arguments. -/
def takeOption (name : String) : List String → OptionValue × List String
  | [] => (.absent, [])
  | [only] => if only == name then (.valueless, []) else (.absent, [only])
  | flag :: value :: rest =>
      if flag == name then (.value value, rest)
      else
        let (found, remaining) := takeOption name (value :: rest)
        (found, flag :: remaining)

/-- Read `--name value` as a string, erroring when the flag is present without one. -/
def takeString (name : String) (args : List String) :
    Except String (Option String × List String) :=
  match takeOption name args with
  | (.absent, rest) => .ok (none, rest)
  | (.valueless, _) => .error s!"{name} expects a value"
  | (.value text, rest) => .ok (some text, rest)

/-- Read `--name value` as a natural number, falling back when the option is absent. -/
def takeNat (name : String) (fallback : Nat) (args : List String) :
    Except String (Nat × List String) :=
  match takeOption name args with
  | (.absent, rest) => .ok (fallback, rest)
  | (.valueless, _) => .error s!"{name} expects a non-negative integer"
  | (.value text, rest) =>
      match text.toNat? with
      | some number => .ok (number, rest)
      | none => .error s!"{name} expects a non-negative integer, got '{text}'"


end Frontier.CLI
