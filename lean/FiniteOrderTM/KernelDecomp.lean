/-
FiniteOrderTM/KernelDecomp.lean

Research note 03, Theorem 3.1 (核分解の特徴づけ / kernel decomposition
characterisation) and Observation 3.0.

Setting.  `f : α → α` is `(m, p)`-preperiodic: `f^[m+p] = f^[m]` pointwise
(`Preperiodic m p f`).  Its *periodic core* is `R := Im(f^[m])`
(`core f m`).  A *kernel decomposition* of `f` is a triple `(e, ι₁, ι₂)`
with `e` idempotent, `Im e = R`, `e = id` on `R`, `ι₁ ι₂` involutions and
    f ∘ e = ι₁ ∘ ι₂ ∘ e      (so `f = ι₁ ∘ ι₂` on `R`).

Theorem 3.1 states, for computable `f : ℕ → ℕ`:
    (i)  `R` is decidable   ⟺   (ii) `f` has a kernel decomposition with
                                      `e, ι₁, ι₂` computable.

What is mechanised.
* (i) ⟹ (ii), structural part: for ANY `(m,p)`-preperiodic `f` on any type
  the projection `e x := f^[ρ x] x`, `ρ x := least j with f^[j] x ∈ R`, is
  an idempotent onto `R` fixing `R`, `f` restricted to `R` has order
  dividing `p`, and `f ∘ e = ι₁ ∘ ι₂ ∘ e` for the two involutions of
  `LocallyFinite.lean` applied to the core rotation `g` (`f` on `R`,
  identity off `R`) — `kernel_decomp_exists`.  The effective layer (that
  `ρ`, `e`, `ι₁`, `ι₂` are computable when `R` is decidable) is the paper's
  argument and is NOT mechanised (it stays at 層2, exactly as the
  effectiveness of Theorem 4.1 does).
* (ii) ⟹ (i), fully: on `ℕ`, a computable idempotent `e` with `Im e = R`
  makes `R` decidable (`core_decidable_of_kernel_decomp`, via
  `computablePred_range_of_computable_idempotent` of NoGo.lean).  This is
  the direction that explains the pre-period-2 no-go (系 3.2).
* Observation 3.0: a literal three-factor form `f = ι₁ ∘ ι₂ ∘ e` with the
  factors mapping `R` into `R` forces pre-period `≤ 1`
  (`three_factor_forces_indexOne`), independently of computability.
-/
import Mathlib
import FiniteOrderTM.Basic
import FiniteOrderTM.PrePeriod
import FiniteOrderTM.LocallyFinite
import FiniteOrderTM.NoGo

namespace PeriodicTM

open Function

variable {α : Type*}

namespace KernelDecomp

attribute [local instance] Classical.propDecidable

/-- `f` is `(m, p)`-preperiodic: `f^[m + p] = f^[m]` pointwise. -/
def Preperiodic (m p : ℕ) (f : α → α) : Prop := ∀ x, f^[m + p] x = f^[m] x

/-- The periodic core `R = Im(f^[m])`. -/
def core (f : α → α) (m : ℕ) : Set α := Set.range f^[m]

variable {f : α → α} {m p : ℕ}

/-- The core is `f`-invariant. -/
theorem apply_mem_core {x : α} (hx : x ∈ core f m) : f x ∈ core f m := by
  obtain ⟨y, hy⟩ := hx
  exact ⟨f y, by rw [← Function.iterate_succ_apply, Function.iterate_succ_apply', hy]⟩

theorem iterate_mem_core {x : α} (hx : x ∈ core f m) (k : ℕ) : f^[k] x ∈ core f m := by
  induction k with
  | zero => simpa using hx
  | succ k ih => rw [Function.iterate_succ_apply']; exact apply_mem_core ih

/-- On the core `f` has order dividing `p`. -/
theorem core_period (hf : Preperiodic m p f) {x : α} (hx : x ∈ core f m) : f^[p] x = x := by
  obtain ⟨y, rfl⟩ := hx
  rw [← Function.iterate_add_apply, add_comm]
  exact hf y

/-- Every point falls into the core within `m` steps. -/
theorem exists_iterate_mem_core (x : α) : ∃ j, f^[j] x ∈ core f m := ⟨m, ⟨x, rfl⟩⟩

variable (f m) in
/-- Number of steps needed to fall into the core: `ρ x = min {j : f^[j] x ∈ R}`. -/
noncomputable def rho (x : α) : ℕ := Nat.find (exists_iterate_mem_core (f := f) (m := m) x)

theorem rho_spec (x : α) : f^[rho f m x] x ∈ core f m :=
  Nat.find_spec (exists_iterate_mem_core (f := f) (m := m) x)

theorem rho_le (x : α) : rho f m x ≤ m :=
  Nat.find_min' (exists_iterate_mem_core (f := f) (m := m) x) ⟨x, rfl⟩

theorem rho_eq_zero_of_mem {x : α} (hx : x ∈ core f m) : rho f m x = 0 :=
  Nat.le_zero.mp (Nat.find_min' (exists_iterate_mem_core (f := f) (m := m) x) (by simpa using hx))

variable (f m) in
/-- The projection onto the core: `e x = f^[ρ x] x`. -/
noncomputable def proj (x : α) : α := f^[rho f m x] x

theorem proj_mem (x : α) : proj f m x ∈ core f m := rho_spec x

theorem proj_eq_self_of_mem {x : α} (hx : x ∈ core f m) : proj f m x = x := by
  simp [proj, rho_eq_zero_of_mem hx]

/-- `e` is idempotent. -/
theorem proj_idem (x : α) : proj f m (proj f m x) = proj f m x :=
  proj_eq_self_of_mem (proj_mem x)

/-- `Im e = R`. -/
theorem range_proj : Set.range (proj f m) = core f m := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩; exact proj_mem y
  · intro hx; exact ⟨x, proj_eq_self_of_mem hx⟩

variable (f m) in
/-- The core rotation: `f` on `R`, identity off `R`. -/
noncomputable def coreRot (x : α) : α := if x ∈ core f m then f x else x

theorem coreRot_of_mem {x : α} (hx : x ∈ core f m) : coreRot f m x = f x := if_pos hx

theorem coreRot_of_not_mem {x : α} (hx : x ∉ core f m) : coreRot f m x = x := if_neg hx

theorem coreRot_iterate_of_mem {x : α} (hx : x ∈ core f m) :
    ∀ k, (coreRot f m)^[k] x = f^[k] x := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, coreRot_of_mem (iterate_mem_core hx k),
      ← Function.iterate_succ_apply']

/-- The core rotation has order dividing `p`. -/
theorem coreRot_orderDividing (hf : Preperiodic m p f) : OrderDividing p (coreRot f m) := by
  intro x
  by_cases hx : x ∈ core f m
  · rw [coreRot_iterate_of_mem hx]; exact core_period hf hx
  · exact Function.iterate_fixed (coreRot_of_not_mem hx) p

/-- `f ∘ e = g ∘ e` for the core rotation `g`. -/
theorem coreRot_proj (x : α) : coreRot f m (proj f m x) = f (proj f m x) :=
  coreRot_of_mem (proj_mem x)

end KernelDecomp

open KernelDecomp

/-! ### Main theorems -/

/-- **Theorem 3.1, (i) ⟹ (ii), structural part.**  Every `(m,p)`-preperiodic
`f` (with `p > 0`) has a kernel decomposition: an idempotent `e` onto the
core `R = Im(f^[m])`, fixing `R`, and two involutions with
`f ∘ e = ι₁ ∘ ι₂ ∘ e`.  (Computability of the three maps when `R` is
decidable is the paper's argument, not mechanised.) -/
theorem kernel_decomp_exists {f : α → α} {m p : ℕ} (hp : 0 < p) (hf : Preperiodic m p f) :
    ∃ e i1 i2 : α → α,
      (∀ x, e (e x) = e x) ∧ Set.range e = core f m ∧ (∀ x ∈ core f m, e x = x) ∧
        IsInvolution i1 ∧ IsInvolution i2 ∧ ∀ x, i1 (i2 (e x)) = f (e x) := by
  have hlf : LocallyFinite (coreRot f m) := fun x => ⟨p, hp, coreRot_orderDividing hf x⟩
  obtain ⟨i1, i2, h1, h2, hgi⟩ := exists_two_involutions_of_locallyFinite hlf
  refine ⟨proj f m, i1, i2, proj_idem, range_proj, fun _ hx => proj_eq_self_of_mem hx,
    h1, h2, fun x => ?_⟩
  rw [hgi, coreRot_proj]

/-- **Theorem 3.1, (ii) ⟹ (i).**  On `ℕ`, a computable idempotent `e` with
`Im e = R` makes the core `R` decidable: `R = Fix(e)`, and `e x = x` is
decidable.  (This is the direction behind the pre-period-2 no-go of
NoGo.lean: there the core is Σ₁-complete, so no kernel decomposition with
computable `e` can exist.) -/
theorem core_decidable_of_kernel_decomp {f e : ℕ → ℕ} {m : ℕ} (he : Computable e)
    (hidem : ∀ x, e (e x) = e x) (hrange : Set.range e = core f m) :
    ComputablePred (fun x => x ∈ core f m) := by
  have h := computablePred_range_of_computable_idempotent he hidem
  rwa [hrange] at h

/-- **Observation 3.0.**  If `f = ι₁ ∘ ι₂ ∘ e` literally, with `e` landing in
the core and `ι₁, ι₂` mapping the core into itself, then `Im f ⊆ R`, i.e.
`f` has pre-period `≤ 1` (`IndexOne p f`): the literal three-factor form only
makes sense at pre-period one, which is why the correct notion at higher
pre-period is the kernel decomposition. -/
theorem three_factor_forces_indexOne {f : α → α} {m p : ℕ} (hf : Preperiodic m p f)
    {e i1 i2 : α → α} (he : ∀ x, e x ∈ core f m)
    (h1 : ∀ x ∈ core f m, i1 x ∈ core f m) (h2 : ∀ x ∈ core f m, i2 x ∈ core f m)
    (hdec : ∀ x, f x = i1 (i2 (e x))) : IndexOne p f := by
  intro x
  have hx : f x ∈ core f m := by rw [hdec]; exact h1 _ (h2 _ (he x))
  rw [Function.iterate_succ_apply]
  exact core_period hf hx

end PeriodicTM
