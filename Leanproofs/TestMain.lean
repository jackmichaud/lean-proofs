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

private def runStorageWorker (root : System.FilePath) (attemptId writer : String) : IO UInt32 := do
  let attempt ← match Frontier.Research.AttemptId.parse attemptId with
    | .ok value => pure value
    | .error message => IO.eprintln message; return 2
  let environment : Frontier.Research.EnvironmentFingerprint := {
    leanVersion := "test"
    mathlibRevision := "test"
    frontierRevision := "test"
    importsHash := "test"
    policyVersion := "test"
  }
  let actor : Frontier.Research.Actor := {
    kind := .tool
    name := writer
    runId := ⟨writer⟩
  }
  let payloads : Array Frontier.Research.Payload := #[
    .metadataUpdated { metadata := { title := "Process concurrency", goal := writer ++ "-first" } },
    .metadataUpdated { metadata := { title := "Process concurrency", goal := writer ++ "-second" } }
  ]
  match ← Frontier.Research.appendPayloads root attempt environment actor payloads with
  | .ok _ => return 0
  | .error message => IO.eprintln message; return 1

unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | ["storage-worker", root, attemptId, writer] =>
      return ← runStorageWorker root attemptId writer
  | [] => pure ()
  | _ => IO.eprintln "invalid frontier-test arguments"; return 2
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := `Leanproofs }] {} (loadExts := true)
  let catalog ← IO.ofExcept <|
    env.evalConst Frontier.Knowledge.Registry {} `Frontier.knowledgeCatalog
  -- A throwaway journal root, and publishing disabled. The tests mutate the journal, and a
  -- suite that wrote into `work/` would destroy the record it is supposed to be protecting.
  let workRoot : System.FilePath := "build" / "test-work"
  IO.FS.createDirAll workRoot
  Frontier.Test.run (← Frontier.CLI.Context.of env catalog workRoot none)
