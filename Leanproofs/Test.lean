/-
Copyright (c) 2026 Jack Michaud. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Michaud
-/

import Leanproofs.Tests.TrustAudit
import Leanproofs.Tests.DraftRetrieval
import Leanproofs.Tests.JournalWork
import Leanproofs.Tests.ProofProtocol
import Leanproofs.Tests.BatchProof
import Leanproofs.Tests.Knowledge
import Leanproofs.Tests.API
import Leanproofs.Tests.ResearchEvents
import Leanproofs.Tests.Fingerprint

/-!
# Frontier audit test runner

The suites live in `Leanproofs.Tests`; this module preserves the single `Frontier.Test.run`
entry point used by `frontier-test`.
-/

open Frontier.CLI

namespace Frontier.Test

def run (context : Context) : IO UInt32 := do
  let suite ← IO.mkRef ({} : Results)
  testAxiomPolicy suite
  testMetadataPredicates suite
  testParsing suite
  testJournalData suite
  testEntryAudit suite context
  testDependencies suite context
  testCorpusBreadth suite context
  testSearch suite context
  testGoalElaboration suite context
  testPremiseRanking suite context
  testDraftChecking suite context
  testDraftIsolation suite context
  testJournalStorage suite context
  testWorkCommands suite context
  testCheckRecording suite context
  testProving suite context
  testBatchProof suite context
  testDispatch suite context
  testKnowledgeModel suite
  testAPI suite context
  testResearchEvents suite
  testFingerprint suite context
  let results ← suite.get
  let total := results.passed + results.failures.size
  for failure in results.failures do
    IO.eprintln s!"FAIL  {failure}"
  IO.println s!"\n{results.passed}/{total} audit tests passed"
  return if results.failures.isEmpty then 0 else 1

end Frontier.Test
