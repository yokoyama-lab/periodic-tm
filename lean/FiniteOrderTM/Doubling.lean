/-
FiniteOrderTM/Doubling.lean

Research note 11, Theorem 11.1 (鏡映複製 / mirror doubling): immune
transversals do not obstruct strong reversibility.

Construction.  For a permutation `ρ` of `β`, the *mirror double*
`ρ̂ = double ρ` acts on `β × Bool` by `ρ` on face `false` and by `ρ⁻¹` on
face `true`; the face swap `ι (x, b) = (x, !b)` is an involution with
`ι ρ̂ ι = ρ̂⁻¹` (it reverses `ρ̂`), and it fixes no `ρ̂`-cycle.  Each face
carries a copy of the cycle partition of `ρ` (`sameCycle_iff`), so `ρ̂`
has no finite cycles when `ρ` has none (`free_double_iff`).

Immunity.  Higman's "every transversal is immune" is used in research/11 in
the equivalent form "every infinite c.e. set meets some cycle twice"; we
take that form as the definition `CycleImmune f CE`, relative to an
abstract class `CE` of "enumerable" sets, and prove that it passes from
`ρ` to `ρ̂` as soon as `CE` is closed under the two face projections
(`cycleImmune_double`).  On `ℕ` with `CE := REPred` (mathlib's r.e.
predicates) the closure is `Partrec.comp`, and `ρ̂`, `ρ̂⁻¹`, `ι` are
computable when `ρ`, `ρ⁻¹` are (`computable_double`, `computable_iota`).

`mirror_doubling` bundles all of this: from any computable, free,
cycle-immune `ρ : Perm ℕ` with computable inverse — such as Higman's
Theorem 3.1 permutation, whose existence is the (literature) input — one
obtains a computable, free, cycle-immune permutation admitting a
computable involutive reverser that fixes no cycle.  This is the whole of
Theorem 11.1 except for the citation of Higman's construction itself.
-/
import Mathlib
import FiniteOrderTM.Basic
import FiniteOrderTM.HalfShift

namespace PeriodicTM

open Equiv

variable {β : Type*}

/-- `f` is *cycle-immune* relative to the class `CE` of sets: every infinite
set in `CE` contains two distinct points on the same `f`-cycle (Higman's
reformulation of "every transversal is immune"). -/
def CycleImmune (f : Perm β) (CE : Set β → Prop) : Prop :=
  ∀ X : Set β, CE X → X.Infinite → ∃ x ∈ X, ∃ y ∈ X, x ≠ y ∧ f.SameCycle x y

namespace Doubling

/-- The underlying map of the mirror double: `ρ` on face `false`, `ρ⁻¹` on
face `true`. -/
def doubleFun (ρ : Perm β) (p : β × Bool) : β × Bool :=
  (bif p.2 then ρ.symm p.1 else ρ p.1, p.2)

/-- The mirror double `ρ̂` of `ρ`, as a permutation of `β × Bool`. -/
def double (ρ : Perm β) : Perm (β × Bool) where
  toFun := doubleFun ρ
  invFun := doubleFun ρ.symm
  left_inv := by rintro ⟨x, b⟩; cases b <;> simp [doubleFun]
  right_inv := by rintro ⟨x, b⟩; cases b <;> simp [doubleFun]

/-- The face swap. -/
def iota (p : β × Bool) : β × Bool := (p.1, !p.2)

variable (ρ : Perm β)

theorem double_apply (x : β) (b : Bool) :
    double ρ (x, b) = (bif b then ρ.symm x else ρ x, b) := rfl

theorem double_inv_apply (x : β) (b : Bool) :
    (double ρ)⁻¹ (x, b) = (bif b then ρ x else ρ.symm x, b) := by
  rw [Perm.inv_def]
  cases b <;> simp [double, doubleFun]

/-- `ι` is an involution. -/
theorem iota_involutive : IsInvolution (iota (β := β)) := by
  rintro ⟨x, b⟩
  simp [iota]

/-- `ι` reverses `ρ̂`: `ι ∘ ρ̂ = ρ̂⁻¹ ∘ ι`. -/
theorem iota_reverses : Reverses (double ρ) iota := by
  rintro ⟨x, b⟩
  cases b <;> simp [iota, double_apply, double_inv_apply]

/-- Powers of `ρ̂` in closed form: `ρ ^ k` on face `false`, `ρ ^ (−k)` on
face `true`. -/
theorem double_zpow (k : ℤ) :
    ∀ (x : β) (b : Bool), ((double ρ) ^ k) (x, b) = (bif b then (ρ ^ (-k)) x else (ρ ^ k) x, b) := by
  induction k with
  | zero => intro x b; cases b <;> simp
  | succ k ih =>
    intro x b
    rw [zpow_add_one, Perm.mul_apply, double_apply, ih]
    cases b
    · simp only [cond_false]
      rw [← Perm.mul_apply, ← zpow_add_one]
    · simp only [cond_true]
      rw [← Perm.inv_def, ← zpow_neg_one, ← Perm.mul_apply, ← zpow_add]
      exact congrArg (fun z => (z, true)) (Reverser.zpow_apply_congr_exp (by ring) x)
  | pred k ih =>
    intro x b
    rw [zpow_sub_one, Perm.mul_apply, double_inv_apply, ih]
    cases b
    · simp only [cond_false]
      rw [← Perm.inv_def, ← Perm.mul_apply, ← zpow_sub_one]
    · simp only [cond_true]
      rw [← Perm.mul_apply, ← zpow_add_one]
      exact congrArg (fun z => (z, true)) (Reverser.zpow_apply_congr_exp (by ring) x)

/-- `ρ̂` preserves faces. -/
theorem double_zpow_snd (k : ℤ) (p : β × Bool) : (((double ρ) ^ k) p).2 = p.2 := by
  rcases p with ⟨x, b⟩
  rw [double_zpow]

/-- `ι` fixes no cycle of `ρ̂`: `ι p` is never on the cycle of `p`
(so the "fixed chains are finitely many" bound of Theorem 7.2 is attained
with zero fixed chains). -/
theorem not_sameCycle_iota (p : β × Bool) : ¬ (double ρ).SameCycle p (iota p) := by
  rcases p with ⟨x, b⟩
  rintro ⟨k, hk⟩
  have h := congrArg Prod.snd hk
  rw [double_zpow] at h
  cases b <;> simp [iota] at h

/-- Each face carries the cycle partition of `ρ` (face `true` with the
orientation reversed). -/
theorem sameCycle_iff (x y : β) (b : Bool) :
    (double ρ).SameCycle (x, b) (y, b) ↔ ρ.SameCycle x y := by
  constructor
  · rintro ⟨k, hk⟩
    rw [double_zpow] at hk
    cases b
    · exact ⟨k, by simpa using congrArg Prod.fst hk⟩
    · exact ⟨-k, by simpa using congrArg Prod.fst hk⟩
  · rintro ⟨k, hk⟩
    cases b
    · exact ⟨k, by rw [double_zpow]; simp [hk]⟩
    · exact ⟨-k, by rw [double_zpow, neg_neg]; simp [hk]⟩

/-- `ρ̂` has no finite cycles iff `ρ` has none (`C₀` membership). -/
theorem free_double_iff : Free (double ρ) ↔ Free ρ := by
  constructor
  · intro h x k hk
    exact h (x, false) k (by rw [double_zpow]; simp [hk])
  · rintro h ⟨x, b⟩ k hk
    rw [double_zpow] at hk
    cases b
    · exact h x k (by simpa using congrArg Prod.fst hk)
    · have := h x (-k) (by simpa using congrArg Prod.fst hk)
      omega

/-- **Inheritance of immunity.**  If the class `CE'` on `β × Bool` is closed
under the two face projections into `CE`, then cycle-immunity passes from
`ρ` to `ρ̂`: an infinite `X ∈ CE'` has an infinite face trace `X_b ∈ CE`,
which meets some `ρ`-cycle twice, and the two points lift to the same
`ρ̂`-cycle on face `b`. -/
theorem cycleImmune_double {CE : Set β → Prop} {CE' : Set (β × Bool) → Prop}
    (hproj : ∀ X, CE' X → ∀ b, CE {x | (x, b) ∈ X}) (h : CycleImmune ρ CE) :
    CycleImmune (double ρ) CE' := by
  intro X hX hinf
  have hsub : X ⊆ (fun x => (x, false)) '' {x | (x, false) ∈ X} ∪
      (fun x => (x, true)) '' {x | (x, true) ∈ X} := by
    rintro ⟨x, b⟩ hx
    cases b
    · exact Or.inl ⟨x, hx, rfl⟩
    · exact Or.inr ⟨x, hx, rfl⟩
  rcases Set.infinite_union.mp (hinf.mono hsub) with h0 | h1
  · obtain ⟨x, hx, y, hy, hne, hc⟩ := h _ (hproj X hX false) (Set.Infinite.of_image _ h0)
    exact ⟨(x, false), hx, (y, false), hy, fun e => hne (congrArg Prod.fst e),
      (sameCycle_iff ρ x y false).mpr hc⟩
  · obtain ⟨x, hx, y, hy, hne, hc⟩ := h _ (hproj X hX true) (Set.Infinite.of_image _ h1)
    exact ⟨(x, true), hx, (y, true), hy, fun e => hne (congrArg Prod.fst e),
      (sameCycle_iff ρ x y true).mpr hc⟩

/-! ### The computable instance on `ℕ` -/

theorem double_inv : (double ρ)⁻¹ = double ρ⁻¹ := by
  refine Equiv.ext ?_
  rintro ⟨x, b⟩
  rw [double_inv_apply, double_apply]
  cases b <;> simp [Perm.inv_def]

/-- `ρ̂` is computable when `ρ` and `ρ⁻¹` are. -/
theorem computable_double (ρ : Perm ℕ) (h : Computable ⇑ρ) (hi : Computable ⇑ρ⁻¹) :
    Computable ⇑(double ρ) := by
  have hc : Computable fun p : ℕ × Bool => (bif p.2 then ρ⁻¹ p.1 else ρ p.1, p.2) :=
    (Computable.cond Computable.snd (hi.comp Computable.fst) (h.comp Computable.fst)).pair
      Computable.snd
  refine hc.of_eq ?_
  rintro ⟨x, b⟩
  cases b <;> simp [double_apply, Perm.inv_def]

/-- `ρ̂⁻¹` is computable when `ρ` and `ρ⁻¹` are. -/
theorem computable_double_inv (ρ : Perm ℕ) (h : Computable ⇑ρ) (hi : Computable ⇑ρ⁻¹) :
    Computable ⇑(double ρ)⁻¹ := by
  rw [double_inv]
  exact computable_double ρ⁻¹ hi (by simpa using h)

/-- The face swap is computable. -/
theorem computable_iota : Computable (iota (β := ℕ)) :=
  (Computable.fst.pair ((Primrec.dom_bool not).to_comp.comp Computable.snd)).of_eq
    fun _ => rfl

/-- Face traces of an r.e. set are r.e. (`Partrec.comp`). -/
theorem rePred_proj {X : Set (ℕ × Bool)} (hX : REPred (· ∈ X)) (b : Bool) :
    REPred (fun x : ℕ => (x, b) ∈ X) :=
  Partrec.comp hX (Computable.id.pair (Computable.const b))

/-- Cycle-immunity with respect to r.e. sets passes from `ρ` to `ρ̂`. -/
theorem cycleImmune_double_re (ρ : Perm ℕ) (h : CycleImmune ρ fun X => REPred (· ∈ X)) :
    CycleImmune (double ρ) fun X => REPred (· ∈ X) :=
  cycleImmune_double ρ (fun X hX b => rePred_proj hX b) h

end Doubling

/-- **Theorem 11.1 (mirror doubling).**  From a computable permutation `ρ` of
`ℕ` with computable inverse, without finite cycles and cycle-immune with
respect to r.e. sets (Higman's Theorem 3.1 provides one), the mirror double
`ρ̂` is again computable with computable inverse, without finite cycles and
cycle-immune, and it admits a computable involutive reverser `ι` that fixes
no `ρ̂`-cycle.  Hence "all transversals are immune" does not decide
conjugacy to the inverse. -/
theorem mirror_doubling (ρ : Perm ℕ) (h : Computable ⇑ρ) (hi : Computable ⇑ρ⁻¹)
    (hfree : Free ρ) (himm : CycleImmune ρ fun X => REPred (· ∈ X)) :
    Computable ⇑(Doubling.double ρ) ∧ Computable ⇑(Doubling.double ρ)⁻¹ ∧
      Free (Doubling.double ρ) ∧ CycleImmune (Doubling.double ρ) (fun X => REPred (· ∈ X)) ∧
      Computable (Doubling.iota (β := ℕ)) ∧ IsInvolution (Doubling.iota (β := ℕ)) ∧
      Reverses (Doubling.double ρ) Doubling.iota ∧
      ∀ p, ¬ (Doubling.double ρ).SameCycle p (Doubling.iota p) :=
  ⟨Doubling.computable_double ρ h hi, Doubling.computable_double_inv ρ h hi,
    (Doubling.free_double_iff ρ).mpr hfree, Doubling.cycleImmune_double_re ρ himm,
    Doubling.computable_iota, Doubling.iota_involutive, Doubling.iota_reverses ρ,
    Doubling.not_sameCycle_iota ρ⟩

end PeriodicTM
