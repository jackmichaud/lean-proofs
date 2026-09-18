/-
Copyright (c) 2026 Jack Michaud. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Michaud
-/

import Leanproofs.Tests.Support

/-! Tests for deterministic and honest environment fingerprints. -/

open Lean

namespace Frontier.Test

private def cleanSources : Fingerprint.SourceProvenance := {
  frontier := .clean "frontier-revision"
  mathlib := .clean "mathlib-revision"
}

private def material : Fingerprint.Material := {
  catalog := "catalog/v1\nclaim:a\n"
  policy := "policy/v1\nallow:propext\n"
}

def testFingerprint (suite : Suite) (context : CLI.Context) : IO Unit := do
  check suite "SHA-256 empty vector is standard"
    (Fingerprint.sha256Hex "" ==
      "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855")
  check suite "SHA-256 abc vector is standard"
    (Fingerprint.sha256Hex "abc" ==
      "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad")
  let started ← IO.monoMsNow
  let snapshot := Fingerprint.snapshot context.env
  let elapsed ← (· - started) <$> IO.monoMsNow
  check suite "module snapshot is populated" (!snapshot.digest.isEmpty)
  check suite "module snapshot stays below the startup budget" (elapsed < 2000)
    s!"snapshot took {elapsed}ms"
  let first := Fingerprint.derive snapshot material cleanSources
  let second := Fingerprint.derive snapshot material cleanSources
  check suite "identical fingerprint inputs are deterministic" (first == second)
  check suite "clean exact revisions permit a content-addressed claim"
    first.reproducibility.isContentAddressed
  check suite "fingerprint Lean version is exact"
    (first.environment.leanVersion == Lean.versionString)
  check suite "clean revisions are preserved exactly"
    (first.environment.frontierRevision == "frontier-revision" &&
      first.environment.mathlibRevision == "mathlib-revision")
  let changedCatalog := Fingerprint.derive snapshot
    { material with catalog := material.catalog ++ "claim:b\n" } cleanSources
  check suite "catalog material changes the identifier"
    (changedCatalog.identifier != first.identifier)
  let changedPolicy := Fingerprint.derive snapshot
    { material with policy := material.policy ++ "deny:unsafe\n" } cleanSources
  check suite "policy material changes the identifier"
    (changedPolicy.identifier != first.identifier)
  let dirty := Fingerprint.derive snapshot material
    { cleanSources with frontier := .dirty (some "frontier-revision") }
  check suite "dirty source is not called content addressed"
    (!dirty.reproducibility.isContentAddressed)
  check suite "dirty revision is explicitly marked unhashed"
    (dirty.environment.frontierRevision == "frontier-revision+dirty-unhashed")
  let unavailable := Fingerprint.derive snapshot material
    { cleanSources with mathlib := .unavailable "test fixture" }
  check suite "unavailable source is not called content addressed"
    (!unavailable.reproducibility.isContentAddressed)
  check suite "unavailable revision is explicit"
    (unavailable.environment.mathlibRevision == "unavailable")
  let unavailablePath : System.FilePath := "build" / "definitely-not-a-git-repository"
  let inspected ← Fingerprint.inspectRepository unavailablePath
  check suite "Git discovery reports an unavailable repository honestly"
    (match inspected with | .unavailable _ => true | _ => false)

end Frontier.Test
