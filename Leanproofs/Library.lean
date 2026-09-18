/-
Copyright (c) 2026 Jack Michaud. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Michaud
-/

import Mathlib

/-!
# The premise corpus

This module exists only to pull all of mathlib into the environment that `frontier` imports at
runtime. It proves nothing and is imported by `Leanproofs` for its side effect on the
environment.

Two capabilities depend on it, and both were quietly crippled without it.

**Premise retrieval.** `frontier search` and `frontier suggest` rank over the theorems that are
*imported*, not over the theorems that exist. When the root module imported only the handful of
mathlib files the catalog's own proofs needed, the corpus was a slice: `Nat.Prime` and
`Matrix.det` resolved, while `MeasureTheory`, `CategoryTheory`, `Complex.exp`, and `Manifold`
returned nothing at all. An agent asking for premises outside that slice got an empty ranking
with no indication that the library simply was not loaded — a missing-library error reported as
a mathematical dead end, which is the failure mode most likely to send it off to reprove
something mathlib already has.

**Draft checking.** `frontier check` cannot import new modules into a live environment, so a
draft may only use what this root module already imports. With a slice loaded, every draft
touching a new area of mathematics required editing the project and a full rebuild before it
could be checked even once.

The cost is import time: roughly twenty seconds, paid once per process. That is what
`frontier serve` exists to amortize, and it is why the documentation tells any caller making
more than a couple of requests to open a session.
-/
