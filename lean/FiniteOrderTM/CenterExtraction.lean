/-
FiniteOrderTM/CenterExtraction.lean

Research note 07, Lemma 7.1 (中心抽出 / centre extraction) and Theorem 7.2
(a reversing involution of a cycle-immune permutation fixes only finitely
many chains), in abstract form.

Setting.  `f : Perm α` without finite orbits (`Free f`) and a reverser
`ι` of `f` (`Reverses f ι`, i.e. `ι f ι⁻¹ = f⁻¹`; involutivity of `ι` is
not needed).  A *centre* is a point `x` with `ι x = x` or `ι x = f x`.

* Lemma 7.1 (`exists_center`): if `ι` maps the orbit of `t` to itself
  (`ι t` lies on the orbit of `t`), that orbit contains a centre.  The
  proof is the paper's: `ι (f^k t) = f^(c−k) t` where `ι t = f^c t`, and the
  centre sits at `k = c/2` (`c` even, a fixed point) or `k = (c−1)/2`
  (`c` odd, `ι x = f x`).  The centre is at distance `|c|/2` from `t`,
  which is what makes the paper's two-sided search terminate; the search
  itself is not mechanised.
* `center_unique`: on a free permutation a fixed orbit has exactly one
  centre (two centres `f^a t`, `f^b t` force `c ∈ {2a, 2a+1} ∩ {2b, 2b+1}`).
* Theorem 7.2, abstract form (`centers_finite`, `fixed_orbits_finite`): if
  `f` is cycle-immune relative to a class `CE` containing the set of
  centres, the set of centres is finite (an infinite set of centres would
  contain two centres on one cycle, contradicting uniqueness), hence only
  finitely many orbits are fixed by `ι`.
* Concrete form on `ℕ` (`fixed_orbits_finite_of_computable`): for
  computable `f`, `ι`, the set of centres is decidable, hence r.e.
  (`ComputablePred.to_re`), so cycle-immunity with respect to r.e. sets
  (the hypothesis satisfied by Higman's permutation, cf. Doubling.lean)
  suffices.  The existence of Higman's permutation is the literature input
  and is not mechanised.
-/
import Mathlib
import FiniteOrderTM.Basic
import FiniteOrderTM.HalfShift
import FiniteOrderTM.Doubling

namespace PeriodicTM

open Equiv

variable {α : Type*}

namespace CenterExtraction

/-- A *centre* of the reverser `ι` on an `f`-orbit: a fixed point of `ι`, or
a point exchanged by `ι` with its successor. -/
def IsCenter (f : Perm α) (ι : α → α) (x : α) : Prop := ι x = x ∨ ι x = f x

instance (f : Perm α) (ι : α → α) [DecidableEq α] : DecidablePred (IsCenter f ι) :=
  fun x => inferInstanceAs (Decidable (ι x = x ∨ ι x = f x))

variable {f : Perm α} {ι : α → α}

/-- **Lemma 7.1 (centre extraction).**  If `ι t` lies on the orbit of `t`,
that orbit contains a centre. -/
theorem exists_center (hι : Reverses f ι) {t : α} (hfix : f.SameCycle t (ι t)) :
    ∃ x, f.SameCycle t x ∧ IsCenter f ι x := by
  obtain ⟨c, hc⟩ := hfix
  have key : ∀ k : ℤ, ι ((f ^ k) t) = (f ^ (c - k)) t := by
    intro k
    rw [Reverses.zpow hι, ← hc, ← Perm.mul_apply, ← zpow_add]
    exact Reverser.zpow_apply_congr_exp (by ring) _
  rcases Int.even_or_odd c with ⟨j, hj⟩ | ⟨j, hj⟩
  · refine ⟨(f ^ j) t, ⟨j, rfl⟩, Or.inl ?_⟩
    rw [key]
    exact Reverser.zpow_apply_congr_exp (by omega) _
  · refine ⟨(f ^ j) t, ⟨j, rfl⟩, Or.inr ?_⟩
    rw [key, Reverser.apply_zpow_apply]
    exact Reverser.zpow_apply_congr_exp (by omega) _

/-- A centre `f^a t` pins the exponent of `ι t = f^c t` to `c ∈ {2a, 2a+1}`. -/
theorem exp_of_center (hι : Reverses f ι) {t : α} {a : ℤ} (ha : IsCenter f ι ((f ^ a) t)) :
    ∃ c : ℤ, ι t = (f ^ c) t ∧ (c = 2 * a ∨ c = 2 * a + 1) := by
  have h := Reverses.zpow hι a t
  rcases ha with ha | ha
  · refine ⟨2 * a, ?_, Or.inl rfl⟩
    have h2 := congrArg (f ^ a) (h.symm.trans ha)
    rw [← Perm.mul_apply, ← zpow_add, add_neg_cancel, zpow_zero, Perm.one_apply,
      ← Perm.mul_apply, ← zpow_add] at h2
    rw [h2]
    exact Reverser.zpow_apply_congr_exp (by ring) _
  · refine ⟨2 * a + 1, ?_, Or.inr rfl⟩
    have h2 := congrArg (f ^ a) (h.symm.trans ha)
    rw [← Perm.mul_apply, ← zpow_add, add_neg_cancel, zpow_zero, Perm.one_apply,
      Reverser.apply_zpow_apply, ← Perm.mul_apply, ← zpow_add] at h2
    rw [h2]
    exact Reverser.zpow_apply_congr_exp (by ring) _

/-- On a free permutation a fixed orbit has at most one centre. -/
theorem center_unique (hfree : Free f) (hι : Reverses f ι) {t : α} {a b : ℤ}
    (ha : IsCenter f ι ((f ^ a) t)) (hb : IsCenter f ι ((f ^ b) t)) :
    (f ^ a) t = (f ^ b) t := by
  obtain ⟨c₁, hc₁, h₁⟩ := exp_of_center hι ha
  obtain ⟨c₂, hc₂, h₂⟩ := exp_of_center hι hb
  have h := hfree t _ (Reverser.zpow_apply_eq_zpow_apply (hc₁.symm.trans hc₂))
  exact Reverser.zpow_apply_congr_exp (by omega) _

/-- **Theorem 7.2, abstract core.**  If `f` is cycle-immune relative to a
class `CE` containing the set of centres, there are only finitely many
centres. -/
theorem centers_finite (hfree : Free f) (hι : Reverses f ι) {CE : Set α → Prop}
    (himm : CycleImmune f CE) (hM : CE {x | IsCenter f ι x}) :
    {x | IsCenter f ι x}.Finite := by
  by_contra hinf
  obtain ⟨x, hx, y, hy, hne, ⟨k, hk⟩⟩ := himm _ hM hinf
  apply hne
  have hx' : IsCenter f ι ((f ^ (0 : ℤ)) x) := by simpa using hx
  have hy' : IsCenter f ι ((f ^ k) x) := by rw [hk]; exact hy
  have := center_unique hfree hι hx' hy'
  simpa [hk] using this

/-- **Theorem 7.2, abstract form.**  Under the same hypotheses, `ι` fixes
only finitely many orbits (each fixed orbit contains a centre, by
Lemma 7.1). -/
theorem fixed_orbits_finite (hfree : Free f) (hι : Reverses f ι) {CE : Set α → Prop}
    (himm : CycleImmune f CE) (hM : CE {x | IsCenter f ι x}) :
    (Set.image (Quotient.mk (Perm.SameCycle.setoid f)) {t | f.SameCycle t (ι t)}).Finite := by
  refine Set.Finite.subset
    ((centers_finite hfree hι himm hM).image (Quotient.mk (Perm.SameCycle.setoid f))) ?_
  rintro q ⟨t, ht, rfl⟩
  obtain ⟨x, hx, hc⟩ := exists_center hι ht
  exact ⟨x, hc, Quotient.sound (s := Perm.SameCycle.setoid f) hx.symm⟩

/-! ### The computable instance on `ℕ` -/

/-- The set of centres of computable `f`, `ι` is decidable. -/
theorem isCenter_computablePred {f : Perm ℕ} {ι : ℕ → ℕ} (hf : Computable ⇑f)
    (hι : Computable ι) : ComputablePred (IsCenter f ι) := by
  apply Computable.computablePred
  obtain ⟨_, heq⟩ := Primrec.eq (α := ℕ)
  have h1 : Computable fun x : ℕ => decide (ι x = x) :=
    (heq.to_comp.comp (hι.pair .id)).of_eq fun x => by simp [id]
  have h2 : Computable fun x : ℕ => decide (ι x = f x) :=
    (heq.to_comp.comp (hι.pair hf)).of_eq fun x => by simp
  exact (Primrec.or.to_comp.comp h1 h2).of_eq fun x => by simp [IsCenter]

/-- **Theorem 7.2 on `ℕ`.**  A computable reverser of a computable, free,
cycle-immune (w.r.t. r.e. sets) permutation fixes only finitely many
orbits. -/
theorem fixed_orbits_finite_of_computable {f : Perm ℕ} {ι : ℕ → ℕ} (hfree : Free f)
    (hι : Reverses f ι) (hf : Computable ⇑f) (hιc : Computable ι)
    (himm : CycleImmune f fun X => REPred (· ∈ X)) :
    (Set.image (Quotient.mk (Perm.SameCycle.setoid f)) {t | f.SameCycle t (ι t)}).Finite :=
  fixed_orbits_finite hfree hι himm (isCenter_computablePred hf hιc).to_re

end CenterExtraction

end PeriodicTM
