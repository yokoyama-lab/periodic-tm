/-
FiniteOrderTM/PrePeriod.lean

The eventually-periodic branch, pre-period one (paper §"...", roadmap A1).

If `f^{p+1} = f` pointwise (the `(1,p)`-periodic / index-one case), then
`f` factors through its idempotent core:

    f = g ∘ e,   e := f^[p]  (idempotent),
                 g := f on the core `Fix(f^[p])`, identity elsewhere,

where `g` is a finite-order bijection (`g^[p] = id`).  Composing with the
finite-order decomposition (`Basic.lean`) gives

    f = ι₁ ∘ ι₂ ∘ e

— two computable involutions and one computable idempotent, i.e. the `(1,p)`
cells collapse onto Nakano's two corner models (two ITMs and one IdTM).

Classical kernel: index-one elements of a monogenic semigroup lie in a
subgroup; the content mechanised here is the effective, global factorisation
on all of `α`.  Everything is elementary and constructive modulo the
`Basic.lean` decomposition.
-/
import FiniteOrderTM.Basic

namespace PeriodicTM

variable {α : Type*} [LinearOrder α]
variable {f : α → α} {p : ℕ}

/-- `f` is `(1,p)`-periodic ("index one, period `p`"): `f^[p+1] = f`. -/
def IndexOne (p : ℕ) (f : α → α) : Prop := ∀ x, f^[p + 1] x = f x

omit [LinearOrder α] in
/-- Every point of the image is fixed by `f^[p]`. -/
theorem core_image (hf : IndexOne p f) (x : α) : f^[p] (f x) = f x := by
  have h := hf x
  rwa [Function.iterate_succ_apply] at h

omit [LinearOrder α] in
/-- The idempotent core map `e := f^[p]` is idempotent (needs `p ≥ 1`). -/
theorem e_idem (hp : 0 < p) (hf : IndexOne p f) (x : α) :
    f^[p] (f^[p] x) = f^[p] x := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  rw [show f^[q + 1] x = f (f^[q] x) from Function.iterate_succ_apply' f q x]
  exact core_image hf (f^[q] x)

/-- The core rotation: `f` on `Fix(f^[p])`, identity elsewhere. -/
def g (f : α → α) (p : ℕ) : α → α := fun x => if f^[p] x = x then f x else x

theorem g_apply_core {x : α} (hx : f^[p] x = x) : g f p x = f x := if_pos hx

theorem g_apply_noncore {x : α} (hx : ¬ f^[p] x = x) : g f p x = x := if_neg hx

omit [LinearOrder α] in
/-- The core `Fix(f^[p])` is `f`-invariant, so iterates of a core point stay
in the core. -/
theorem mem_core_iterate (hf : IndexOne p f) {x : α} (hx : f^[p] x = x) :
    ∀ k, f^[p] (f^[k] x) = f^[k] x := by
  intro k
  cases k with
  | zero => simpa using hx
  | succ k =>
    rw [Function.iterate_succ_apply']
    exact core_image hf (f^[k] x)

/-- On the core, `g` agrees with `f` along all iterates. -/
theorem g_iterate_core (hf : IndexOne p f) {x : α} (hx : f^[p] x = x) :
    ∀ k, (g f p)^[k] x = f^[k] x := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih,
        g_apply_core (mem_core_iterate hf hx k), ← Function.iterate_succ_apply' f k]

/-- `g` is a finite-order bijection: `g^[p] = id`. -/
theorem g_orderDividing (hf : IndexOne p f) : OrderDividing p (g f p) := by
  intro x
  by_cases hx : f^[p] x = x
  · rw [g_iterate_core hf hx p]; exact hx
  · exact Function.iterate_fixed (g_apply_noncore hx) p

/-- The factorisation `f = g ∘ e` with `e := f^[p]`. -/
theorem f_eq_g_comp_e (hp : 0 < p) (hf : IndexOne p f) (x : α) :
    g f p (f^[p] x) = f x := by
  rw [g_apply_core (e_idem hp hf x), ← Function.iterate_succ_apply' f p]
  exact hf x

/-- **Pre-period one decomposition** (roadmap A1): every `(1,p)`-periodic
computable bijection is `ι₁ ∘ ι₂ ∘ e` with `ι₁, ι₂` involutions and `e`
idempotent. -/
theorem index_one_decomp (hp : 0 < p) (hf : IndexOne p f) :
    ∃ i1 i2 e : α → α,
      IsInvolution i1 ∧ IsInvolution i2 ∧ (∀ x, e (e x) = e x) ∧
        ∀ x, i1 (i2 (e x)) = f x := by
  obtain ⟨i1, i2, h1, h2, hgi⟩ := exists_two_involutions hp (g_orderDividing hf)
  refine ⟨i1, i2, f^[p], h1, h2, e_idem hp hf, fun x => ?_⟩
  rw [hgi (f^[p] x)]
  exact f_eq_g_comp_e hp hf x

end PeriodicTM
