/-
Copyright (c) 2026 Jack Michaud. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Michaud
-/

import Mathlib.Data.Nat.Basic

/-!
# Catalan's conjecture

This module records the natural-number form of Catalan's conjecture, also known as
Mihăilescu's theorem: the only consecutive perfect powers above `1` are `8` and `9`.

Mihăilescu proved this in 2002. It is registered here with Frontier status `open` because
*this repository* has not formalized the proof, and literature state `proved` because
mathematics has. The sanity checks below guard the formalization itself: they witness that
the hypotheses of `conjecture` are satisfiable, so the statement is not vacuously true.
-/

namespace Catalan

/-- Catalan's conjecture / Mihăilescu's theorem for natural numbers.

If `x ^ a` is exactly one more than `y ^ b`, with both bases and exponents strictly greater
than `1`, then the powers are the classical exceptional pair `3 ^ 2` and `2 ^ 3`.
-/
def conjecture : Prop :=
  ∀ x y a b : ℕ,
    1 < x →
    1 < y →
    1 < a →
    1 < b →
    x ^ a = y ^ b + 1 →
    x = 3 ∧ a = 2 ∧ y = 2 ∧ b = 3

/-- Sanity check: the exceptional pair in Catalan's conjecture is indeed a solution. -/
theorem exceptional_solution : (3 : ℕ) ^ 2 = 2 ^ 3 + 1 := by
  rfl

/-- Sanity check against vacuity: the hypotheses of `conjecture` are satisfiable, so
`conjecture` is not trivially true for want of any instance to constrain. -/
theorem hypotheses_satisfiable :
    ∃ x y a b : ℕ, 1 < x ∧ 1 < y ∧ 1 < a ∧ 1 < b ∧ x ^ a = y ^ b + 1 :=
  ⟨3, 2, 2, 3, by decide, by decide, by decide, by decide, exceptional_solution⟩

/-- Sanity check by exhausted bounded search: `conjecture` has no counterexample with bases
below `12` and exponents below `6`. This does not prove the conjecture, but it does rule out
the most common formalization errors, which show up as small counterexamples. -/
theorem no_small_counterexample :
    ∀ x ∈ List.range 12, ∀ y ∈ List.range 12, ∀ a ∈ List.range 6, ∀ b ∈ List.range 6,
      1 < x → 1 < y → 1 < a → 1 < b → x ^ a = y ^ b + 1 →
      x = 3 ∧ a = 2 ∧ y = 2 ∧ b = 3 := by
  decide

end Catalan
