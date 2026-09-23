/-
FiniteOrderTM/HalfShift.lean

Research note 13, Theorem 13.1 (半シフト補正 / half-shift correction).

Setting.  `f : Perm α` and a *reverser* `g` of `f`, i.e. `g ∘ f = f⁻¹ ∘ g`
(`Reverses f g`).  Assume the action of `g` on the orbit space is an
involution: `g (g x)` lies on the orbit of `x` for every `x`, so that
`g (g x) = f ^ t x (x)` for some integer shift `t x`.  Then the explicit
correction
        ι x := g (f ^ s x (x)),      s x := −⌈t x / 2⌉ = −((t x + 1) / 2)
is an involution that still reverses `f`.  This is the construction of
research/13, and `ι` is computable from `g`, `f` and `t` (a composition of
computable maps; the computability layer itself is not mechanised).

What is mechanised.
* `halfShift_involution`, `halfShift_reverses`: the two verifications, for
  an arbitrary shift datum (`t` orbit-constant and antisymmetric under `g`,
  `ShiftData`).  The integer identity `−⌈t/2⌉ + ⌈−t/2⌉ = −t` of the paper is
  discharged by `omega` (it is `t + (−t+1)/2 − (t+1)/2 = 0` in floor
  division).
* `half_shift_correction_free`: on a permutation without finite orbits
  (`Free f`: `f ^ k x = x → k = 0`), the two side conditions on `t` are
  *derived* from `g (g x) = f ^ t x (x)` and `Reverses f g` (uniqueness of
  the shift on a ℤ-chain, as in the paper: `t(C') = −t(C)`), so the theorem
  needs only the raw hypothesis "the orbit action of `g` is an involution".
* `strongly_reversible_iff_orbit_involutive_reverser`: the 問B
  characterisation of research/13 — a free permutation is strongly
  reversible (has an involutive reverser) iff it has a reverser whose orbit
  action is an involution.

The finite-orbit part of the paper's proof ("有限軌道は定理 4.1 の軌道内反射
で処理") is not glued in here; it is covered non-effectively by
`perm_strongly_reversible` (PermTwoInvolutions.lean) and effectively by
`LocallyFinite.lean` when all orbits are finite.
-/
import Mathlib
import FiniteOrderTM.Basic
import FiniteOrderTM.PermTwoInvolutions

namespace PeriodicTM

open Equiv

variable {α : Type*}

/-- `g` reverses `f`: `g ∘ f = f⁻¹ ∘ g` (i.e. `g` conjugates `f` to `f⁻¹`). -/
def Reverses (f : Perm α) (g : α → α) : Prop := ∀ x, g (f x) = f⁻¹ (g x)

/-- `f` has no finite orbits: `f ^ k x = x` only for `k = 0`. -/
def Free (f : Perm α) : Prop := ∀ (x : α) (k : ℤ), (f ^ k) x = x → k = 0

namespace Reverser

variable {f : Perm α} {g : α → α}

theorem Reverses.inv_apply (hg : Reverses f g) (x : α) : g (f⁻¹ x) = f (g x) := by
  have h := hg (f⁻¹ x)
  rw [perm_apply_inv_self] at h
  rw [h, perm_apply_inv_self]

/-- A reverser turns every power into the inverse power:
`g (f ^ k x) = f ^ (−k) (g x)`. -/
theorem Reverses.zpow (hg : Reverses f g) (k : ℤ) :
    ∀ x, g ((f ^ k) x) = (f ^ (-k)) (g x) := by
  induction k with
  | zero => intro x; simp
  | succ k ih =>
    intro x
    rw [zpow_add_one, Perm.mul_apply, ih, hg, ← Perm.mul_apply, ← zpow_sub_one]
    exact zpow_apply_congr_exp (by ring) _
  | pred k ih =>
    intro x
    rw [zpow_sub_one, Perm.mul_apply, ih, hg.inv_apply, ← Perm.mul_apply, ← zpow_add_one]
    exact zpow_apply_congr_exp (by ring) _

/-- The inverse form: `f ^ k (g x) = g (f ^ (−k) x)`. -/
theorem Reverses.zpow_apply (hg : Reverses f g) (k : ℤ) (x : α) :
    (f ^ k) (g x) = g ((f ^ (-k)) x) := by
  rw [hg.zpow, neg_neg]

variable (f g) in
/-- A *shift datum* for a reverser `g`: `g² = f ^ t` pointwise, with `t`
constant along orbits and antisymmetric under `g` (`t(g C) = −t(C)`). -/
structure ShiftData where
  t : α → ℤ
  gg : ∀ x, g (g x) = (f ^ t x) x
  t_apply : ∀ x, t (f x) = t x
  t_g : ∀ x, t (g x) = - t x

variable (S : ShiftData f g)

theorem ShiftData.t_inv_apply (x : α) : S.t (f⁻¹ x) = S.t x := by
  have h := S.t_apply (f⁻¹ x)
  rwa [perm_apply_inv_self] at h

theorem ShiftData.t_zpow (k : ℤ) : ∀ x, S.t ((f ^ k) x) = S.t x := by
  induction k with
  | zero => intro x; simp
  | succ k ih => intro x; rw [zpow_add_one, Perm.mul_apply, ih, S.t_apply]
  | pred k ih => intro x; rw [zpow_sub_one, Perm.mul_apply, ih, S.t_inv_apply]

/-- The half shift `s = −⌈t/2⌉`, in floor division `−((t + 1) / 2)`. -/
def ShiftData.s (x : α) : ℤ := -((S.t x + 1) / 2)

/-- The corrected reverser `ι x = g (f ^ s x (x))`. -/
def halfShift (x : α) : α := g ((f ^ S.s x) x)

/-- **Theorem 13.1, involutivity.** -/
theorem halfShift_involution (hg : Reverses f g) : IsInvolution (halfShift S) := by
  intro x
  -- notation: y := f ^ s x, so ι x = g y; t y = t x, t (g y) = −t x
  set y := (f ^ S.s x) x with hy
  have hty : S.t y = S.t x := S.t_zpow _ x
  have htg : S.t (g y) = - S.t x := by rw [S.t_g, hty]
  have hs' : S.s (g y) = -((- S.t x + 1) / 2) := by
    unfold ShiftData.s; rw [htg]
  have hsx : S.s x = -((S.t x + 1) / 2) := rfl
  show g ((f ^ S.s (g y)) (g y)) = x
  rw [hg.zpow_apply, S.gg, S.t_zpow, hty, hs', hy, hsx, ← Perm.mul_apply, ← zpow_add,
    ← Perm.mul_apply, ← zpow_add]
  exact zpow_apply_eq_self_of_exp_zero (by omega) _

/-- **Theorem 13.1, reversal.**  The corrected map still reverses `f`. -/
theorem halfShift_reverses (hg : Reverses f g) : Reverses f (halfShift S) := by
  intro x
  show g ((f ^ S.s (f x)) (f x)) = f⁻¹ (g ((f ^ S.s x) x))
  have hs : S.s (f x) = S.s x := by unfold ShiftData.s; rw [S.t_apply]
  rw [hs, ← hg, ← Perm.mul_apply, ← zpow_add_one, add_comm, apply_zpow_apply]

/-! ### Deriving the shift datum on a free permutation -/

variable (hfree : Free f) (hg : Reverses f g) (t : α → ℤ) (ht : ∀ x, g (g x) = (f ^ t x) x)
include hfree hg ht

/-- On a free permutation the shift is constant along orbits. -/
theorem shift_apply (x : α) : t (f x) = t x := by
  -- g (g (f x)) = f (g (g x)) = f ^ (t x + 1) x, and also = f ^ (t (f x) + 1) x
  have h1 : g (g (f x)) = (f ^ (t x + 1)) x := by
    rw [hg, hg.inv_apply, ht, apply_zpow_apply, add_comm]
  have h2 : g (g (f x)) = (f ^ (t (f x) + 1)) x := by
    rw [ht, zpow_add_one, Perm.mul_apply]
  have h3 := zpow_apply_eq_zpow_apply (h2.symm.trans h1)
  have h4 := hfree x _ h3
  omega

/-- On a free permutation the shift is antisymmetric under `g`. -/
theorem shift_g (x : α) : t (g x) = - t x := by
  -- g (g (g x)) = g (f ^ t x (x)) = f ^ (−t x) (g x), and also = f ^ (t (g x)) (g x)
  have h1 : g (g (g x)) = (f ^ (- t x)) (g x) := by
    conv_lhs => rw [ht x]
    rw [hg.zpow]
  have h2 : g (g (g x)) = (f ^ t (g x)) (g x) := ht (g x)
  have h3 := zpow_apply_eq_zpow_apply (h2.symm.trans h1)
  have h4 := hfree (g x) _ h3
  omega

/-- The shift datum derived from the raw hypothesis on a free permutation. -/
def shiftDataOfFree : ShiftData f g where
  t := t
  gg := ht
  t_apply := shift_apply hfree hg t ht
  t_g := shift_g hfree hg t ht

end Reverser

/-! ### Main theorems -/

/-- **Theorem 13.1 (half-shift correction), general form.**  A reverser `g`
with a shift datum yields the explicit involutive reverser
`ι x = g (f ^ (−⌈t x/2⌉) x)`. -/
theorem half_shift_correction {f : Perm α} {g : α → α} (hg : Reverses f g)
    (S : Reverser.ShiftData f g) :
    ∃ ι : α → α, IsInvolution ι ∧ Reverses f ι :=
  ⟨Reverser.halfShift S, Reverser.halfShift_involution S hg, Reverser.halfShift_reverses S hg⟩

/-- **Theorem 13.1 on a free permutation.**  If `f` has no finite orbits and
`g` is a reverser whose orbit action is an involution (`g² x` lies on the
orbit of `x`), then `f` is strongly reversible, with an involutive reverser
computed uniformly from `g` and the shifts. -/
theorem half_shift_correction_free {f : Perm α} {g : α → α} (hfree : Free f)
    (hg : Reverses f g) (t : α → ℤ) (ht : ∀ x, g (g x) = (f ^ t x) x) :
    ∃ ι : α → α, IsInvolution ι ∧ Reverses f ι :=
  half_shift_correction hg (Reverser.shiftDataOfFree hfree hg t ht)

/-- **問B characterisation (research/13).**  A free permutation is strongly
reversible iff it has a reverser whose orbit action is an involution. -/
theorem strongly_reversible_iff_orbit_involutive_reverser {f : Perm α} (hfree : Free f) :
    (∃ ι : α → α, IsInvolution ι ∧ Reverses f ι) ↔
      ∃ g : α → α, Reverses f g ∧ ∃ t : α → ℤ, ∀ x, g (g x) = (f ^ t x) x := by
  constructor
  · rintro ⟨ι, hι, hrev⟩
    exact ⟨ι, hrev, fun _ => 0, fun x => by simp [hι x]⟩
  · rintro ⟨g, hg, t, ht⟩
    exact half_shift_correction_free hfree hg t ht

end PeriodicTM
