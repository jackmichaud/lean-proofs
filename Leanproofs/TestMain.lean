/-
Copyright (c) 2026 Jack Michaud. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Michaud
-/

import Lean
import Leanproofs.Registry
import Leanproofs.CLI
import Leanproofs.Test

/-!
# The `frontier-test` executable

The audit tests run against a real imported environment, because most of what they assert is
about resolving declarations, elaborating drafts, and walking proof terms — none of which has
meaning against a mock. This executable therefore imports the project at runtime exactly the
way `Leanproofs.Main` does, and for the same reason: see that module's docstring.
-/

open Lean

unsafe def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := `Leanproofs }] {} (loadExts := true)
  let catalog ← IO.ofExcept <| env.evalConst (Array Frontier.Entry) {} `Frontier.catalog
  -- A throwaway journal root, and publishing disabled. The tests mutate the journal, and a
  -- suite that wrote into `work/` would destroy the record it is supposed to be protecting.
  let workRoot : System.FilePath := "build" / "test-work"
  IO.FS.createDirAll workRoot
  Frontier.Test.run (← Frontier.CLI.Context.of env catalog workRoot none)
