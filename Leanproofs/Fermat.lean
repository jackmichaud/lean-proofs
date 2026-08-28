/-
Copyright (c) 2026 Jack Michaud. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Michaud
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.FieldTheory.Finite.Basic

/-!
# Fermat's Little Theorem, from scratch

We prove: if `p` is prime and `a : ℤ` with `¬ (p ∣ a)`, then `a ^ (p-1) ≡ 1 [ZMOD p]`.
And the companion form: for any `a : ℤ`, `a ^ p ≡ a [ZMOD p]`.

Strategy (Lagrange-flavored, "from scratch"):
1. `(ZMod p)ˣ` is a finite group of order `p - 1` (since `ZMod p` is a field when `p` is prime).
2. In any finite group `G`, `g ^ (Fintype.card G) = 1` (this is `pow_card_eq_one`,
   itself a corollary of Lagrange: order-of-element divides group order).
3. Transport back to `ZMod p` and then to `ℤ`.
-/

namespace FermatFromScratch

open ZMod

/-- Fermat's little theorem in `(ZMod p)ˣ`: any unit raised to `p-1` is `1`. -/
theorem units_pow_card_sub_one_eq_one
    (p : ℕ) [Fact p.Prime] (u : (ZMod p)ˣ) :
    u ^ (p - 1) = 1 := by
  -- Cardinality of the unit group of a finite field of size p is p - 1.
  have hcard : Fintype.card (ZMod p)ˣ = p - 1 := ZMod.card_units p
  have h := pow_card_eq_one (G := (ZMod p)ˣ) (x := u)
  rw [hcard] at h
  exact h

/-- Fermat's little theorem in `ZMod p`: if `a ≠ 0`, then `a ^ (p-1) = 1`. -/
theorem pow_card_sub_one_eq_one
    {p : ℕ} [Fact p.Prime] {a : ZMod p} (ha : a ≠ 0) :
    a ^ (p - 1) = 1 := by
  -- Since `ZMod p` is a field and `a ≠ 0`, `a` is a unit.
  have hu : IsUnit a := Ne.isUnit ha
  obtain ⟨u, rfl⟩ := hu
  -- Reduce to the units version by pushing the cast through the power.
  have h := units_pow_card_sub_one_eq_one p u
  have := congrArg (Units.val) h
  simpa [Units.val_pow_eq_pow_val] using this

/-- Companion form: `a ^ p = a` in `ZMod p`, for every `a` (including `0`). -/
theorem pow_card (p : ℕ) [hp : Fact p.Prime] (a : ZMod p) : a ^ p = a := by
  by_cases ha : a = 0
  · -- 0^p = 0, since p ≥ 1.
    have hp1 : 1 ≤ p := hp.out.one_lt.le
    subst ha
    exact zero_pow (Nat.one_le_iff_ne_zero.mp hp1)
  · -- a^p = a^(p-1) * a = 1 * a = a
    have hp1 : 1 ≤ p := hp.out.one_lt.le
    have : a ^ p = a ^ (p - 1) * a := by
      rw [← pow_succ, Nat.sub_add_cancel hp1]
    rw [this, pow_card_sub_one_eq_one ha, one_mul]

/-- Integer form: for a prime `p` and `a : ℤ` with `¬ (p ∣ a)`,
    `a ^ (p-1) ≡ 1 (mod p)`. -/
theorem int_pow_card_sub_one
    {p : ℕ} [Fact p.Prime] {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) :
    (a : ZMod p) ^ (p - 1) = 1 := by
  have : (a : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact pow_card_sub_one_eq_one this

/-- Integer companion form: `a^p ≡ a (mod p)` for any integer `a`. -/
theorem int_pow_card {p : ℕ} [Fact p.Prime] (a : ℤ) :
    (a : ZMod p) ^ p = (a : ZMod p) :=
  pow_card p (a : ZMod p)

end FermatFromScratch
