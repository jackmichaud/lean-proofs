/-
Copyright (c) 2026 Jack Michaud. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Michaud
-/

import Leanproofs.Research.Model
import Leanproofs.Registry

/-!
# Reproducible environment fingerprints

This module fingerprints the imported-module manifest of a loaded `Lean.Environment` together with
caller-supplied canonical catalog and policy serializations. Exact clean repository revisions
provide the content identity of imported source. A dirty or unavailable repository is reported
honestly and never receives a content-addressed claim.

The pure `derive` entry point is suitable for deterministic callers and tests. `capture` adds local
Git discovery without modifying the repository or accessing the network.
-/

open Lean

namespace Frontier.Fingerprint

/-- Git provenance for one source tree. Dirty contents are deliberately not summarized by a commit. -/
inductive RepositoryState where
  | clean (revision : String)
  | dirty (revision? : Option String)
  | unavailable (reason : String)
  deriving BEq, Inhabited, Repr

def RepositoryState.revisionText : RepositoryState → String
  | .clean revision => revision
  | .dirty (some revision) => s!"{revision}+dirty-unhashed"
  | .dirty none => "unknown+dirty-unhashed"
  | .unavailable _ => "unavailable"

def RepositoryState.isClean : RepositoryState → Bool
  | .clean _ => true
  | _ => false

/-- Why a fingerprint can or cannot be treated as a reproducible content address. -/
inductive Reproducibility where
  | contentAddressed
  | nonContentAddressed (reasons : Array String)
  deriving BEq, Inhabited, Repr

def Reproducibility.isContentAddressed : Reproducibility → Bool
  | .contentAddressed => true
  | .nonContentAddressed _ => false

/-- Explicit semantic material supplied by the catalog and trust-policy owners.

Both strings must already be in their normalized, versioned form. Length-prefixed framing in this
module prevents ambiguity, but normalization remains the caller's responsibility. -/
structure Material where
  catalog : String
  policy : String
  deriving BEq, Inhabited, Repr

/-- Versioned deterministic serialization of the complete normalized knowledge graph. Lean's
version is part of the outer digest, so changes to `Repr` across toolchains cannot collide. -/
def catalogMaterial (catalog : Knowledge.Registry) : String :=
  "frontier-knowledge/v1\n" ++ reprStr catalog

structure SourceProvenance where
  frontier : RepositoryState
  mathlib : RepositoryState
  deriving BEq, Inhabited, Repr

/-- Canonical summary of the loaded environment's module identity. -/
structure EnvironmentSnapshot where
  digest : String
  importCount : Nat
  deriving BEq, Inhabited, Repr

structure Result where
  /-- Stable identifier for the loaded declarations, explicit material, versions, and provenance. -/
  identifier : String
  /-- Event-model projection for later integration into `CLI.Context`. -/
  environment : Research.EnvironmentFingerprint
  reproducibility : Reproducibility
  sources : SourceProvenance
  deriving BEq, Inhabited, Repr

/-! ## SHA-256

The implementation is intentionally small and streaming. It avoids Lean's `Hashable`, whose output
is an implementation detail, and avoids platform hashing commands.
-/

private structure Sha256 where
  state : Array UInt32
  pending : ByteArray := ByteArray.empty
  bytesSeen : UInt64 := 0

private def initialState : Array UInt32 := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

private def roundConstants : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

private def rotateRight (x : UInt32) (n : Nat) : UInt32 :=
  (x >>> UInt32.ofNat n) ||| (x <<< UInt32.ofNat (32 - n))

private def wordAt (bytes : ByteArray) (offset : Nat) : UInt32 :=
  (UInt32.ofNat bytes[offset]!.toNat <<< (24 : UInt32)) |||
  (UInt32.ofNat bytes[offset + 1]!.toNat <<< (16 : UInt32)) |||
  (UInt32.ofNat bytes[offset + 2]!.toNat <<< (8 : UInt32)) |||
  UInt32.ofNat bytes[offset + 3]!.toNat

private def compress (state : Array UInt32) (block : ByteArray) : Array UInt32 := Id.run do
  let mut words := Array.replicate 64 (0 : UInt32)
  for i in [0:16] do
    words := words.set! i (wordAt block (i * 4))
  for i in [16:64] do
    let x := words[i - 15]!
    let y := words[i - 2]!
    let s0 := rotateRight x 7 ^^^ rotateRight x 18 ^^^ (x >>> (3 : UInt32))
    let s1 := rotateRight y 17 ^^^ rotateRight y 19 ^^^ (y >>> (10 : UInt32))
    words := words.set! i (words[i - 16]! + s0 + words[i - 7]! + s1)
  let mut a := state[0]!
  let mut b := state[1]!
  let mut c := state[2]!
  let mut d := state[3]!
  let mut e := state[4]!
  let mut f := state[5]!
  let mut g := state[6]!
  let mut h := state[7]!
  for i in [0:64] do
    let sum1 := rotateRight e 6 ^^^ rotateRight e 11 ^^^ rotateRight e 25
    let choose := (e &&& f) ^^^ ((~~~e) &&& g)
    let temp1 := h + sum1 + choose + roundConstants[i]! + words[i]!
    let sum0 := rotateRight a 2 ^^^ rotateRight a 13 ^^^ rotateRight a 22
    let majority := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let temp2 := sum0 + majority
    h := g
    g := f
    f := e
    e := d + temp1
    d := c
    c := b
    b := a
    a := temp1 + temp2
  return #[state[0]! + a, state[1]! + b, state[2]! + c, state[3]! + d,
    state[4]! + e, state[5]! + f, state[6]! + g, state[7]! + h]

private def Sha256.pushBytes (sha : Sha256) (bytes : ByteArray) : Sha256 := Id.run do
  let all := sha.pending ++ bytes
  let fullSize := all.size - all.size % 64
  let mut state := sha.state
  for offset in [0:fullSize:64] do
    state := compress state (all.extract offset (offset + 64))
  return {
    state
    pending := all.extract fullSize all.size
    bytesSeen := sha.bytesSeen + UInt64.ofNat bytes.size
  }

private def Sha256.pushString (sha : Sha256) (value : String) : Sha256 :=
  sha.pushBytes value.toUTF8

private def pushFramed (sha : Sha256) (tag value : String) : Sha256 :=
  sha.pushString s!"{tag}:{value.toUTF8.size}:{value}\n"

private def uint64Bytes (value : UInt64) : ByteArray := Id.run do
  let mut result := ByteArray.empty
  for shift in [56, 48, 40, 32, 24, 16, 8, 0] do
    result := result.push (UInt8.ofNat ((value >>> UInt64.ofNat shift).toNat &&& 0xff))
  return result

private def Sha256.finish (sha : Sha256) : Array UInt32 :=
  let bitLength := sha.bytesSeen * 8
  let withMarker := sha.pushBytes (ByteArray.empty.push 0x80)
  let zeroCount := (56 + 64 - withMarker.pending.size % 64) % 64
  let padded := withMarker.pushBytes (ByteArray.empty ++ ByteArray.mk (Array.replicate zeroCount 0))
  (padded.pushBytes (uint64Bytes bitLength)).state

private def hexWord (word : UInt32) : String :=
  let digits := String.ofList (Nat.toDigits 16 word.toNat)
  String.ofList (List.replicate (8 - digits.length) '0') ++ digits

private def Sha256.hex (sha : Sha256) : String :=
  "".intercalate (sha.finish.toList.map hexWord)

/-- Stable SHA-256 for canonical material supplied to this module. -/
def sha256Hex (value : String) : String :=
  ({ state := initialState : Sha256 }).pushString value |>.hex

/-! ## Canonical environment serialization -/

def snapshot (env : Environment) : EnvironmentSnapshot := Id.run do
  let modules := env.allImportedModuleNames.toList.map Name.toString |>.mergeSort
  let manifest := "\n".intercalate <|
    ["frontier-loaded-environment-v1", Lean.versionString, env.mainModule.toString,
      toString env.header.trustLevel] ++ modules
  return { digest := s!"sha256:{sha256Hex manifest}", importCount := modules.length }

private def combinedDigest (environment : EnvironmentSnapshot) (material : Material)
    (sources : SourceProvenance) : String := Id.run do
  let mut sha : Sha256 := { state := initialState }
  sha := pushFramed sha "format" "frontier-environment-v1"
  sha := pushFramed sha "loaded-environment" environment.digest
  sha := pushFramed sha "catalog" material.catalog
  sha := pushFramed sha "policy" material.policy
  sha := pushFramed sha "frontier-source" sources.frontier.revisionText
  sha := pushFramed sha "mathlib-source" sources.mathlib.revisionText
  return sha.hex

private def sourceProblem (name : String) : RepositoryState → Option String
  | .clean _ => none
  | .dirty _ => some s!"{name} working tree has unhashed changes"
  | .unavailable reason => some s!"{name} revision unavailable: {reason}"

/-- Deterministically derive a fingerprint from a reusable environment snapshot and explicit material.

Callers can inject source provenance, making this function pure and straightforward to test. -/
def derive (environment : EnvironmentSnapshot) (material : Material)
    (sources : SourceProvenance) : Result :=
  let digest := combinedDigest environment material sources
  let problems := #[sourceProblem "Frontier" sources.frontier,
    sourceProblem "mathlib" sources.mathlib].filterMap id
  let reproducibility := if problems.isEmpty then .contentAddressed else .nonContentAddressed problems
  {
    identifier := s!"frontier-env-v1:sha256:{digest}"
    environment := {
      leanVersion := Lean.versionString
      mathlibRevision := sources.mathlib.revisionText
      frontierRevision := sources.frontier.revisionText
      importsHash := s!"sha256:{digest}"
      policyVersion := s!"sha256:{sha256Hex material.policy}"
    }
    reproducibility
    sources
  }

/-- Convenience form for one-off pure callers. Reuse `snapshot` when deriving multiple variants. -/
def fromEnvironment (env : Environment) (material : Material) (sources : SourceProvenance) : Result :=
  derive (snapshot env) material sources

private def trimmedOutput? (output : IO.Process.Output) : Option String :=
  if output.exitCode != 0 then none
  else
    let value := output.stdout.trimAscii.toString
    if value.isEmpty then none else some value

private def gitOutput (root : System.FilePath) (args : Array String) : IO (Option String) := do
  try
    return trimmedOutput? (← IO.Process.output {
      cmd := "git"
      args := #["--no-optional-locks", "-C", root.toString] ++ args
    })
  catch _ => return none

/-- Lean source and package metadata are the files relevant to the loaded environment. Narrow
pathspecs avoid scanning generated package assets while still detecting untracked Lean inputs. -/
private def relevantPathspecs : Array String := #[
  "*.lean", "lakefile.lean", "lakefile.toml", "lean-toolchain", "lake-manifest.json"]

private def gitRun (root : System.FilePath) (args : Array String) : IO (Option IO.Process.Output) := do
  try
    return some (← IO.Process.output {
      cmd := "git"
      args := #["--no-optional-locks", "-C", root.toString] ++ args
    })
  catch _ => return none

/-- Inspect a local Git tree without refreshing or modifying its index. Tracked changes and
untracked Lean/package inputs both make the source non-content-addressed. -/
def inspectRepository (root : System.FilePath) : IO RepositoryState := do
  let revision? ← gitOutput root #["rev-parse", "--verify", "HEAD"]
  let tracked? ← gitRun root
    (#["diff-index", "--quiet", "--ignore-submodules=none", "HEAD", "--"] ++ relevantPathspecs)
  let untracked? ← gitRun root
    (#["ls-files", "--others", "--exclude-standard", "--"] ++ relevantPathspecs)
  match tracked?, untracked? with
  | some tracked, some untracked =>
      if tracked.exitCode > 1 || untracked.exitCode != 0 then
        return .unavailable "Git could not inspect relevant source changes"
      let dirty := tracked.exitCode == 1 || !untracked.stdout.trimAscii.isEmpty
      return if dirty then .dirty revision? else
        match revision? with
        | some revision => .clean revision
        | none => .unavailable "HEAD is unavailable"
  | _, _ => return .unavailable "Git is unavailable or the path is not a repository"

/-- Discover local source provenance and derive a fingerprint. No network or Git mutation occurs. -/
def capture (env : Environment) (material : Material)
    (frontierRoot : System.FilePath := ".")
    (mathlibRoot : System.FilePath := ".lake/packages/mathlib") : IO Result := do
  let sources := {
    frontier := ← inspectRepository frontierRoot
    mathlib := ← inspectRepository mathlibRoot
  }
  return derive (snapshot env) material sources

end Frontier.Fingerprint
