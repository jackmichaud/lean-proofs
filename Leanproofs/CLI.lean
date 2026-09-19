/-
Copyright (c) 2026 Jack Michaud. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Michaud
-/

import Leanproofs.Frontier.MCP

/-!
# Frontier CLI

Audits the research catalog against a compiled Lean environment, searches all imported Lean
declarations, records work in progress, and exports a reusable machine-readable theorem index.

This module deliberately does *not* import `Leanproofs.Catalog`. The executable has to import
the project environment at runtime with initializers enabled, and re-initializing modules that
are also statically linked into the binary crashes the process. `Leanproofs.Main` therefore
links only `Lean` and this module, imports the project, and hands the catalog in as data. See
that module for the full explanation.
-/

open Lean

namespace Frontier.CLI

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
  | ["serve"] => runServe context
  | ["mcp"] => MCP.run context
  | "serve" :: _ => emit asJson (.failure "serve takes no arguments")
  | "mcp" :: _ => emit asJson (.failure "mcp takes no arguments")
  | _ => emit asJson (← compute context rest)

end Frontier.CLI
