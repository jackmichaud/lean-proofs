/-
Copyright (c) 2026 Jack Michaud. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Michaud
-/

import Lean
import Leanproofs.Registry
import Leanproofs.CLI

/-!
# The `frontier` executable

This module is deliberately thin, and its import list is load-bearing.

Rendering a Lean proposition with its real notation — `↑a ^ p = ↑a` rather than
`Eq (HPow.hPow …) …` — requires the delaborators that mathlib registers through environment
extensions. Those are only populated when the environment is imported with `loadExts := true`,
which in turn requires `enableInitializersExecution`.

Running initializers for a module that is *already statically linked into this binary*
crashes the process. So the executable must not link the modules it is going to import: it
links `Lean`, the plain data types in `Leanproofs.Registry`, and the command implementations
in `Leanproofs.CLI`, then imports `Leanproofs` at runtime and reads `Frontier.catalog` out of
the resulting environment as data.
-/

open Lean

unsafe def loadEnvironment : IO Environment := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  importModules #[{ module := `Leanproofs }] {} (loadExts := true)

/-- Read the catalog out of the imported environment. The name cannot be resolved at compile
time — that is the whole point of the split — so it is spelled with a single backtick. -/
unsafe def loadCatalog (env : Environment) : IO (Array Frontier.Entry) :=
  IO.ofExcept <| env.evalConst (Array Frontier.Entry) {} `Frontier.catalog

unsafe def main (args : List String) : IO UInt32 := do
  match Frontier.CLI.runWithoutEnvironment? args with
  | some action => action
  | none =>
      let env ← loadEnvironment
      let catalog ← loadCatalog env
      Frontier.CLI.run (Frontier.CLI.Context.of env catalog) args
