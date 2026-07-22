/-
Copyright (c) 2026 Tetsuo Yokoyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuo Yokoyama
-/
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Dynamics.PeriodicPts.Lemmas

/-!
# Eventually-periodic (preperiodic) points

A point `x : α` is **eventually-periodic** (*preperiodic*) under `f : α → α` with
pre-period `m : ℕ` and period `p : ℕ` if `f^[m + p] x = f^[m] x`.

The orbit of `x` has a "rho" (ρ) shape: a tail of length `m` leading into a cycle of
length dividing `p`.  The `m = 0` case reduces to ordinary periodicity `IsPeriodicPt f p x`.

## Main definitions

* `Function.IsEventuallyPeriodicPt f m p x` : `f^[m + p] x = f^[m] x`.
* `Function.eventuallyPeriodicPts f` : the set of all eventually-periodic points of `f`.
* `Function.idempotentExp m p` : the smallest multiple of `p` that is `≥ m` (the
  "idempotent exponent" `k` satisfying `f^[2k] x = f^[k] x` on eventually-periodic orbits).

## Main statements

* `Function.isEventuallyPeriodicPt_iff_isPeriodicPt_iterate` :
  `x` is `(m, p)`-eventually-periodic iff `f^[m] x` is `p`-periodic.
* `Function.isEventuallyPeriodicPt_zero` :
  the `m = 0` case is exactly `IsPeriodicPt f p x`.
* `Function.IsEventuallyPeriodicPt.succ_pre` / `.add_pre` / `.mul_period` :
  closure under pre-period increment and period multiplication.
* `Function.IsPeriodicPt.isEventuallyPeriodicPt` :
  every periodic point is `(m, p)`-eventually-periodic for any `m`.
* `Function.periodicPts_subset_eventuallyPeriodicPts` :
  `periodicPts f ⊆ eventuallyPeriodicPts f`.
* `Function.IsEventuallyPeriodicPt.idempotent` :
  `f^[2 * idempotentExp m p] x = f^[idempotentExp m p] x`.

## References

* Howie, *Fundamentals of Semigroup Theory* (1995), §1.2 (monogenic semigroup index/period)

## Tags

periodic points, eventually-periodic, preperiodic, pre-period, idempotent exponent
-/

namespace Function

open Set

variable {α : Type*} {f : α → α} {m p : ℕ} {x : α}

/-! ### Definition and key equivalence -/

/-- A point `x` is eventually-periodic (preperiodic) with pre-period `m` and period `p` if
`f^[m + p] x = f^[m] x`.  When `m = 0` this is `IsPeriodicPt f p x`. -/
def IsEventuallyPeriodicPt (f : α → α) (m p : ℕ) (x : α) : Prop :=
  f^[m + p] x = f^[m] x

/-- `IsEventuallyPeriodicPt f m p x` iff `f^[m] x` is a `p`-periodic point of `f`. -/
theorem isEventuallyPeriodicPt_iff_isPeriodicPt_iterate :
    IsEventuallyPeriodicPt f m p x ↔ IsPeriodicPt f p (f^[m] x) := by
  simp only [IsEventuallyPeriodicPt, IsPeriodicPt, IsFixedPt, ← iterate_add_apply, add_comm p m]

@[simp]
theorem isEventuallyPeriodicPt_zero :
    IsEventuallyPeriodicPt f 0 p x ↔ IsPeriodicPt f p x := by
  simp [isEventuallyPeriodicPt_iff_isPeriodicPt_iterate]

namespace IsEventuallyPeriodicPt

/-- The `m`-th iterate of an eventually-periodic point is periodic with period `p`. -/
theorem isPeriodicPt_iterate (h : IsEventuallyPeriodicPt f m p x) :
    IsPeriodicPt f p (f^[m] x) :=
  isEventuallyPeriodicPt_iff_isPeriodicPt_iterate.mp h

/-- Increasing the pre-period by one. -/
theorem succ_pre (h : IsEventuallyPeriodicPt f m p x) :
    IsEventuallyPeriodicPt f (m + 1) p x := by
  unfold IsEventuallyPeriodicPt
  have heq : m + 1 + p = (m + p) + 1 := by omega
  rw [heq]
  simp only [iterate_succ_apply']
  exact congr_arg f h

/-- Increasing the pre-period by any amount. -/
theorem add_pre (h : IsEventuallyPeriodicPt f m p x) (k : ℕ) :
    IsEventuallyPeriodicPt f (m + k) p x := by
  induction k with
  | zero => simpa
  | succ k ih =>
    have heq : m + (k + 1) = (m + k) + 1 := by omega
    rw [heq]
    exact ih.succ_pre

/-- Multiplying the period. -/
theorem mul_period (h : IsEventuallyPeriodicPt f m p x) (n : ℕ) :
    IsEventuallyPeriodicPt f m (p * n) x :=
  isEventuallyPeriodicPt_iff_isPeriodicPt_iterate.mpr (h.isPeriodicPt_iterate.mul_const n)

/-- `f x` is eventually-periodic if `x` is. -/
theorem apply (h : IsEventuallyPeriodicPt f m p x) :
    IsEventuallyPeriodicPt f m p (f x) :=
  isEventuallyPeriodicPt_iff_isPeriodicPt_iterate.mpr (by
    rw [← iterate_succ_apply, iterate_succ_apply']
    exact h.isPeriodicPt_iterate.apply)

/-- Any iterate of an eventually-periodic point is eventually-periodic. -/
theorem apply_iterate (h : IsEventuallyPeriodicPt f m p x) (k : ℕ) :
    IsEventuallyPeriodicPt f m p (f^[k] x) := by
  induction k with
  | zero => simpa
  | succ k ih =>
    rw [iterate_succ_apply']
    exact ih.apply

end IsEventuallyPeriodicPt

/-! ### Connection with periodic points -/

/-- Every periodic point is `(m, p)`-eventually-periodic for any pre-period `m`. -/
theorem IsPeriodicPt.isEventuallyPeriodicPt (h : IsPeriodicPt f p x) (m : ℕ) :
    IsEventuallyPeriodicPt f m p x :=
  isEventuallyPeriodicPt_iff_isPeriodicPt_iterate.mpr (h.apply_iterate m)

/-! ### The set of eventually-periodic points -/

/-- The set of eventually-periodic points of `f`. -/
def eventuallyPeriodicPts (f : α → α) : Set α :=
  { x | ∃ m p, 0 < p ∧ IsEventuallyPeriodicPt f m p x }

@[simp]
theorem mem_eventuallyPeriodicPts :
    x ∈ eventuallyPeriodicPts f ↔ ∃ m p, 0 < p ∧ IsEventuallyPeriodicPt f m p x :=
  Iff.rfl

theorem periodicPts_subset_eventuallyPeriodicPts :
    periodicPts f ⊆ eventuallyPeriodicPts f := by
  intro x hx
  rw [mem_periodicPts] at hx
  obtain ⟨p, hp, hper⟩ := hx
  exact ⟨0, p, hp, isEventuallyPeriodicPt_zero.mpr hper⟩

/-! ### Idempotent exponent -/

/-- The smallest multiple of `p` that is `≥ m`: `p * ⌈m / p⌉`.
This is the "idempotent exponent" `k` satisfying `f^[2k] x = f^[k] x` on eventually-periodic
orbits.  When `p = 0` or `m = 0`, this is `0`. -/
def idempotentExp (m p : ℕ) : ℕ := p * ((m + p - 1) / p)

theorem idempotentExp_dvd (m p : ℕ) : p ∣ idempotentExp m p :=
  Dvd.dvd.mul_right (dvd_refl p) _

theorem le_idempotentExp {p : ℕ} (m : ℕ) (hp : 0 < p) : m ≤ idempotentExp m p := by
  unfold idempotentExp
  -- p * ⌊(m+p-1)/p⌋ + (m+p-1)%p = m+p-1, and (m+p-1)%p < p ≤ p,
  -- so p * ⌊(m+p-1)/p⌋ ≥ m+p-1-(p-1) = m.
  have h1 := Nat.div_add_mod (m + p - 1) p
  have h2 := Nat.mod_lt (m + p - 1) hp
  omega

theorem idempotentExp_lt_add {p : ℕ} (m : ℕ) (hp : 0 < p) :
    idempotentExp m p < m + p := by
  unfold idempotentExp
  -- p * ⌊(m+p-1)/p⌋ ≤ (m+p-1)/p * p ≤ m+p-1 < m+p.
  have hbound : p * ((m + p - 1) / p) ≤ m + p - 1 :=
    Nat.mul_comm _ _ ▸ Nat.div_mul_le_self (m + p - 1) p
  omega

/-- `f^[idempotentExp m p]` is idempotent on the orbit of an `(m, p)`-eventually-periodic point.
-/
theorem IsEventuallyPeriodicPt.idempotent
    (h : IsEventuallyPeriodicPt f m p x) (hp : 0 < p) :
    f^[2 * idempotentExp m p] x = f^[idempotentExp m p] x := by
  set k := idempotentExp m p with hk_def
  have hkm : m ≤ k := le_idempotentExp m hp
  have hkdvd : p ∣ k := idempotentExp_dvd m p
  -- f^[k] x is p-periodic: write f^[k] x = f^[k-m] (f^[m] x) where f^[m] x is p-periodic.
  have hfkper : IsPeriodicPt f p (f^[k] x) := by
    have heq : f^[k] x = f^[k - m] (f^[m] x) := by
      rw [← iterate_add_apply, Nat.sub_add_cancel hkm]
    rw [heq]
    exact h.isPeriodicPt_iterate.apply_iterate _
  -- f^[2k] x = f^[k] (f^[k] x) = f^[k] x because f^[k] x is p-periodic and p ∣ k.
  calc f^[2 * k] x
      = f^[k] (f^[k] x) := by rw [two_mul, iterate_add_apply]
    _ = f^[k] x         := hfkper.trans_dvd hkdvd

end Function
