/-
FiniteOrderTM/Dihedral.lean

#3 (new theory): the dihedral / ℤ-n symmetry of the two-involution decomposition.

`Basic.lean` decomposes a finite-order `f` as `f = iota1 ∘ iota2` with both
factors involutions (`finite_order_eq_two_involutions`).  The two reflections
`iota1`, `iota2` generate a dihedral action: `f` is the rotation `iota1 ∘ iota2`,
and the REVERSED product `iota2 ∘ iota1` is the inverse rotation `f⁻¹`.  So the
inverse decomposes with the *same two involutions in the opposite order*.

This is proved here purely from involution algebra and the factorisation — no
`ZMod` arithmetic (unlike `Basic.lean`'s reflection proofs).  Two consequences,
both on the paper's time-symmetry theme:

* `exists_inverse_two_involutions`: `f⁻¹` is a product of the same two
  involutions (reversed), exhibiting the full `⟨iota1, iota2⟩ ≅ D_n` structure.
* `finite_order_conjugate_to_inverse`: there is an involution `σ` (namely
  `iota2`) with `f ∘ σ ∘ f ∘ σ = id`, i.e. `σ` conjugates `f` to `f⁻¹` — every
  finite-order bijection is *time-symmetric* via an involution.
-/
import FiniteOrderTM.Basic

namespace PeriodicTM

open Function

variable {α : Type*} [LinearOrder α] {f : α → α} {n : ℕ}

/-- **Reverse product is a right inverse.**  `f ∘ (iota2 ∘ iota1) = id`.  Pure
involution algebra: `f (iota2 (iota1 x)) = iota1 (iota2 (iota2 (iota1 x)))`
`= iota1 (iota1 x) = x`. -/
theorem iota_inv_right [NeZero n] (hf : OrderDividing n f) (x : α) :
    f (iota2 f n hf (iota1 f n hf x)) = x := by
  have h := iota1_iota2 hf (iota2 f n hf (iota1 f n hf x))
  rw [iota2_involution hf (iota1 f n hf x), iota1_involution hf x] at h
  exact h.symm

/-- **Reverse product is a left inverse.**  `(iota2 ∘ iota1) ∘ f = id`. -/
theorem iota_inv_left [NeZero n] (hf : OrderDividing n f) (x : α) :
    iota2 f n hf (iota1 f n hf (f x)) = x := by
  have h := iota1_iota2 hf x
  rw [← h, iota1_involution hf (iota2 f n hf x), iota2_involution hf x]

/-- **Time symmetry (conjugation form).**  `f ∘ iota2 ∘ f ∘ iota2 = id`: the
reflection `iota2` conjugates `f` to its inverse.  Holds because
`f (iota2 x) = iota1 x` definitionally, so this is `f (iota2 (iota1 x)) = x`. -/
theorem finite_order_time_symmetric_conj [NeZero n] (hf : OrderDividing n f) (x : α) :
    f (iota2 f n hf (f (iota2 f n hf x))) = x := by
  show f (iota2 f n hf (iota1 f n hf x)) = x
  exact iota_inv_right hf x

/-- **The inverse decomposes with the same two involutions, reversed** (the
dihedral structure).  For a finite-order `f`: there are two involutions `i1`,
`i2` with `i1 ∘ i2 = f` AND `i2 ∘ i1 = f⁻¹` (stated as the two inverse laws).
The classical fact that `f` is a product of two involutions, sharpened to show
the inverse uses the *same pair in reverse* — so `⟨i1, i2⟩` acts as `D_n`. -/
theorem exists_inverse_two_involutions (hn : 0 < n) (hf : OrderDividing n f) :
    ∃ i1 i2 : α → α, IsInvolution i1 ∧ IsInvolution i2 ∧
      (∀ x, i1 (i2 x) = f x) ∧
      (∀ x, f (i2 (i1 x)) = x) ∧ (∀ x, i2 (i1 (f x)) = x) :=
  haveI : NeZero n := ⟨hn.ne'⟩
  ⟨iota1 f n hf, iota2 f n hf, iota1_involution hf, iota2_involution hf,
    iota1_iota2 hf, iota_inv_right hf, iota_inv_left hf⟩

/-- **Every finite-order bijection is time-symmetric via an involution.**  There
is an involution `σ` with `f ∘ σ ∘ f ∘ σ = id` (equivalently `f ∘ σ` is itself an
involution, i.e. `σ` conjugates `f` to `f⁻¹`).  This recasts the decomposition in
the reversible-computing / time-symmetry idiom that motivates the paper. -/
theorem finite_order_conjugate_to_inverse (hn : 0 < n) (hf : OrderDividing n f) :
    ∃ σ : α → α, IsInvolution σ ∧ ∀ x, f (σ (f (σ x))) = x :=
  haveI : NeZero n := ⟨hn.ne'⟩
  ⟨iota2 f n hf, iota2_involution hf, finite_order_time_symmetric_conj hf⟩

end PeriodicTM
