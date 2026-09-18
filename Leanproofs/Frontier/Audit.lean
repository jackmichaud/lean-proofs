/-
Copyright (c) 2026 Jack Michaud. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Michaud
-/

import Leanproofs.Frontier.Core

open Lean

namespace Frontier.CLI

/-! ## Auditing -/

open Knowledge

def certificateShapeIsValid (env : Environment) (formalization : Formalization)
    (statementInfo certificateInfo : ConstantInfo) : Bool :=
  match statementExpr? statementInfo with
  | none => false
  | some statement =>
      match formalization.status with
      | .conditional | .proved | .independent | .undecidable =>
          Kernel.isDefEqGuarded env {} certificateInfo.type statement
      | .disproved =>
          let negated := mkApp (.const ``Not []) statement
          Kernel.isDefEqGuarded env {} certificateInfo.type negated
      | _ => true

def evidenceMatchesStatus (status : RepositoryStatus)
    (method? : Option CertificateMethod) : Bool :=
  match status, method? with
  | .formalizing, none | .open, none => true
  | .conditional, some .conditionalProof => true
  | .proved, some .directProof => true
  | .disproved, some .counterexample => true
  | .independent, some .modelConstruction | .independent, some .metatheorem => true
  | .undecidable, some .reduction | .undecidable, some .metatheorem => true
  | _, _ => false

/-- A `status`/`literature` pair that cannot both be true. -/
def literatureContradiction (status : RepositoryStatus)
    (literature : LiteratureConclusion) : Option String :=
  match status, literature with
  | .proved, .refuted =>
      some "this repository proves the statement while the literature field says it is refuted"
  | .disproved, .affirmed =>
      some "this repository refutes the statement while the literature field says it is proved"
  | _, _ => none

structure AuditedSanityCheck where
  name : Name
  type : String
  deriving Inhabited

structure Audit where
  entry : RegisteredClaim
  statementType : String
  statementAxioms : Array String
  certificateType? : Option String
  declarationKind : String
  dependencies : Array String
  axioms : Array String
  sanityChecks : Array AuditedSanityCheck
  errors : Array String

def Audit.isValid (audit : Audit) : Bool := audit.errors.isEmpty

def auditEntry (context : Context) (entry : RegisteredClaim) : StateT ReachCache IO Audit := do
  let env := context.env
  let mut errors := #[]
  let mut statementType := "<missing>"
  let mut kind := "missing"
  let mut statementAxioms : Array Name := #[]
  -- Statement.
  let statementInfo? := context.find? entry.statement
  match statementInfo? with
  | none =>
      errors := errors.push s!"statement declaration '{entry.statement}' does not exist"
  | some info =>
      statementType ← prettyStatement env info
      kind := declarationKind info
      if (statementExpr? info).isNone then
        errors := errors.push
          s!"statement declaration '{entry.statement}' does not denote a proposition"
      -- A statement built out of `sorry` would make an `open` entry look clean, so audit it
      -- even when there is no certificate to audit.
      let statementReach ← reach context entry.statement
      statementAxioms := statementReach.axiomArray
      errors := errors ++ axiomPolicyErrors "the statement" statementAxioms
  -- Certificate.
  let mut certificateType? := none
  let mut axiomNames : Array Name := #[]
  let mut dependencies : Array String := #[]
  match entry.certificate? with
  | none =>
      if entry.status.isClosed then
        errors := errors.push s!"closed status '{entry.status.toString}' requires a certificate"
  | some certificate =>
      match context.find? certificate.declaration with
      | none =>
          errors := errors.push s!"certificate declaration '{certificate.declaration}' does not exist"
      | some certificateInfo =>
          certificateType? := some (← prettyType env certificateInfo)
          if !entry.status.isClosed then
            errors := errors.push
              s!"status '{entry.status.toString}' cannot have a closing certificate"
          match certificateInfo with
          | .thmInfo _ => pure ()
          | _ => errors := errors.push s!"certificate '{certificate.declaration}' is not a Lean theorem"
          if let some statementInfo := statementInfo? then
            if !certificateShapeIsValid env entry.formalization statementInfo certificateInfo then
              errors := errors.push
                s!"certificate type does not match the '{entry.status.toString}' claim"
          let certificateReach ← reach context certificate.declaration
          axiomNames := certificateReach.axiomArray
          dependencies := certificateReach.catalogArray entry.id
          errors := errors ++ axiomPolicyErrors s!"certificate '{certificate.declaration}'" axiomNames
  -- Entries with no certificate take their dependencies from the statement.
  if entry.certificate?.isNone && statementInfo?.isSome then
    dependencies := (← reach context entry.statement).catalogArray entry.id
  -- Sanity checks.
  let mut sanityChecks : Array AuditedSanityCheck := #[]
  for check in entry.sanityChecks do
    match context.find? check.declaration with
    | none => errors := errors.push s!"sanity check '{check.declaration}' does not exist"
    | some info =>
        match info with
        | .thmInfo _ => pure ()
        | _ => errors := errors.push s!"sanity check '{check.declaration}' is not a Lean theorem"
        let checkReach ← reach context check.declaration
        errors := errors ++ axiomPolicyErrors s!"sanity check '{check.declaration}'" checkReach.axiomArray
        sanityChecks := sanityChecks.push { name := check.declaration, type := (← prettyType env info) }
  if !entry.status.isClosed && entry.sanityChecks.isEmpty then
    errors := errors.push
      "an unresolved entry needs at least one sanity check; a formal statement nothing has \
       been proved about is exactly where mis-formalization hides (see docs/adding-results.md)"
  -- Metadata.
  if entry.claim.id.value.trimAscii.isEmpty then
    errors := errors.push "entry id cannot be empty"
  if entry.claim.title.trimAscii.isEmpty then
    errors := errors.push "entry title cannot be empty"
  let method? := entry.certificate?.map (·.method)
  if !evidenceMatchesStatus entry.status method? then
    let evidence := method?.map CertificateMethod.toString |>.getD "none"
    errors := errors.push
      s!"evidence '{evidence}' is incompatible with status '{entry.status.toString}'"
  if entry.status.isRelative && (entry.baseTheory?.getD "").trimAscii.isEmpty then
    errors := errors.push
      s!"status '{entry.status.toString}' is relative and must name the formalized base theory \
         or decision problem in `baseTheory?`"
  if entry.literature.requiresCitation &&
      !entry.citations.any (fun citation => !citation.display.trimAscii.isEmpty) then
    errors := errors.push
      s!"literature state '{entry.literature.toString}' makes a claim about existing \
         mathematics and requires a citation"
  if let some contradiction := literatureContradiction entry.status entry.literature then
    errors := errors.push contradiction
  if !isIsoDate entry.claim.created then
    errors := errors.push s!"created '{entry.claim.created}' is not an ISO-8601 YYYY-MM-DD date"
  if !isIsoDate entry.claim.updated then
    errors := errors.push s!"updated '{entry.claim.updated}' is not an ISO-8601 YYYY-MM-DD date"
  if entry.claim.authors.isEmpty then
    errors := errors.push "every entry needs at least one human author"
  return {
    entry
    statementType
    statementAxioms := statementAxioms.map (·.toString)
    certificateType?
    declarationKind := kind
    dependencies
    axioms := axiomNames.map (·.toString)
    sanityChecks
    errors
  }

def auditCatalog (context : Context) : IO (Array Audit × Array String) := do
  let (audits, _) ← (context.catalog.entries.mapM (auditEntry context)).run {}
  return (audits, context.catalog.validationErrors)

/-! ## Draft checking

`frontier check` elaborates a Lean file against the already-imported environment and reports
Lean's diagnostics plus the axiom policy, without touching the catalog. This is the loop an
author or an agent iterates in: a draft is a file, not a registry edit.

The catalog is deliberately not consulted for *membership* here — a draft has no id, no status,
and no metadata to audit. What it does reuse is the registry index, so the report can say which
catalog results the draft's proofs actually depend on.

**This elaborates the file in this process.** Lean elaboration is not a sandboxed pure
computation: `#eval` performs IO, `run_cmd` and macros execute during elaboration, and
`initialize` blocks run on import. `frontier check` is therefore a local developer tool for
files you would have compiled anyway, and is *not* a submission endpoint. Accepting drafts from
an untrusted source requires the process isolation described in
`docs/retrieval-and-agents.md`. -/

/-- One declaration produced by a draft file. -/
structure DraftDeclaration where
  name : Name
  kind : String
  type : String
  axioms : Array Name
  /-- Catalog entries the declaration's proof term reaches. -/
  dependencies : Array String
  errors : Array String
  deriving Inhabited

/-- The result of elaborating a draft file. -/
structure DraftReport where
  /-- Rendered Lean diagnostics, in source order, already prefixed with `file:line:col`. -/
  diagnostics : Array String
  /-- Whether any diagnostic was an error. Warnings do not fail a draft. -/
  hasErrors : Bool
  declarations : Array DraftDeclaration
  /-- Failures that prevented elaboration from being meaningful at all. -/
  fatal : Array String

def DraftReport.policyErrorCount (report : DraftReport) : Nat :=
  report.declarations.foldl (init := 0) fun total declaration =>
    total + declaration.errors.size

def DraftReport.isClean (report : DraftReport) : Bool :=
  report.fatal.isEmpty && !report.hasErrors && report.policyErrorCount == 0

/-- Declarations added to `after` that were not already in `before`.

After `importModules` the constant map is switched to its second stage, so everything
elaborated afterwards lands in `map₂` and the new declarations can be read off directly
instead of re-folding all of mathlib. The `find?` guard keeps the answer correct if that
representation ever changes; it just makes the walk cost proportional to the draft. -/
def newDeclarations (before after : Environment) : Array Name :=
  let names := after.constants.map₂.foldl (init := #[]) fun names name _ =>
    if (before.find? name).isNone && !name.isInternal then names.push name else names
  names.qsort Name.lt

/-- Elaborate `path` against `context.env` and audit whatever it defines.

Imports in the draft's header are checked against the loaded environment rather than acted on:
the process cannot import new modules into a live environment, so a draft may only use what
`Leanproofs` already imports. Saying so explicitly is the difference between a confusing
"unknown identifier" cascade and an actionable message.

`heartbeats` bounds elaboration. Non-termination is the ordinary failure mode of a generated
proof, not an edge case, so the default is finite; `0` disables the limit. -/
def checkDraft (context : Context) (path : System.FilePath) (heartbeats : Nat) :
    IO DraftReport := do
  unless ← path.pathExists do
    return { diagnostics := #[], hasErrors := false, declarations := #[]
             fatal := #[s!"draft file '{path}' does not exist"] }
  let contents ← IO.FS.readFile path
  let inputContext := Parser.mkInputContext contents path.toString
  let (header, parserState, headerMessages) ← Parser.parseHeader inputContext
  let mut fatal := #[]
  for name in (Elab.headerToImports header (includeInit := false)).map (·.module) do
    unless context.env.allImportedModuleNames.contains name do
      fatal := fatal.push
        s!"draft imports '{name}', which is not in the loaded environment; a draft can only \
           use modules that `Leanproofs` already imports, so add the import there and rebuild"
  -- Stop here rather than elaborating anyway. The draft asked for declarations this
  -- environment does not have, so every use of one is about to be reported as an unknown
  -- identifier — the cascade this check exists to replace, printed *underneath* the one
  -- message that explains it. Worse, a draft whose missing import happens not to matter
  -- elaborates clean and reports a declaration list beside a fatal error.
  unless fatal.isEmpty do
    return { diagnostics := #[], hasErrors := false, declarations := #[], fatal }
  let options := ppOptions.set `maxHeartbeats heartbeats
  let frontendState ← Elab.IO.processCommands inputContext parserState
    (Elab.Command.mkState context.env headerMessages options)
  let messages := frontendState.commandState.messages
  let mut diagnostics := #[]
  for message in messages.toArray do
    diagnostics := diagnostics.push (← message.toString)
  -- Audit the draft's declarations in the *post-elaboration* environment, against the same
  -- registry index the catalog audit uses, so a draft's axioms and catalog reuse are reported
  -- by exactly the code that gates a real entry.
  let draftEnv := frontendState.commandState.env
  let draftContext := { context with env := draftEnv }
  let mut declarations := #[]
  let mut cache : ReachCache := {}
  for name in newDeclarations context.env draftEnv do
    let some info := draftEnv.find? name | continue
    let (declarationReach, next) ← (reach draftContext name).run cache
    cache := next
    let axioms := declarationReach.axiomArray
    declarations := declarations.push {
      name
      kind := declarationKind info
      type := ← prettyType draftEnv info
      axioms
      dependencies := declarationReach.catalogArray ""
      errors := axiomPolicyErrors s!"'{name}'" axioms
    }
  return { diagnostics, hasErrors := messages.hasErrors, declarations, fatal }

end Frontier.CLI
