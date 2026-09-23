/-
FiniteOrderTM/PermTwoInvolutions.lean

Structural core of research note 07, Theorem 7.3 ("orbit-decidable ⟹ product
of two computable involutions"), and of Lemma 4.3 (single ℤ-chain).

Theorem 7.3 is an *effectiveness* statement: if the orbit relation of a
computable permutation `f` is decidable (equivalently, `f` has a c.e.
transversal `T`), then `f` is the product of two *computable* involutions.
Its proof has two layers:

1. (effective layer, NOT mechanised here — it stays at 層2) by dovetailing
   the enumeration of `T` with the two-sided walk along the orbit of `x`
   one computes an *orbit datum*: a representative `rep x ∈ T` of the orbit
   of `x`, and a position `pos x : ℤ` with `f ^ pos x (rep x) = x`;

2. (structural layer, mechanised here) from ANY such orbit datum the two
   reflections
        ι₂ x := f ^ (−pos x) (rep x),      ι₁ := f ∘ ι₂
   are involutions with `ι₁ ∘ ι₂ = f`; moreover `ι₂` conjugates `f` to
   `f⁻¹`.  This is exactly the construction written in research/07
   ("`t` を原点として鎖ごとの反射 `ι₂(f^k t) = f^{−k} t`, `ι₁ = f∘ι₂`").

The structural layer is proved for an arbitrary permutation `f : Perm α` of
an arbitrary type, with orbits of any shape (finite cycles and infinite
ℤ-chains alike) and with NO uniqueness assumption on `pos`: the exponent
arithmetic is done through the cancellation lemma
`zpow_apply_eq_zpow_apply` in the group `Perm α`, so the finite-orbit and
infinite-orbit cases need no separate treatment (contrast `Basic.lean` /
`LocallyFinite.lean`, which work in `ZMod m`).

Taking `rep` to be a classical choice of orbit representatives
(`Quotient.out` of the `SameCycle` class) gives the classical theorem that
EVERY permutation is a product of two involutions
(`perm_eq_two_involutions`) and is conjugate to its inverse by an
involution (`perm_strongly_reversible`) — the non-effective shadow of
Theorem 7.3, generalising `locallyFinite_eq_two_involutions` (which needs
all orbits finite) to arbitrary orbits.
-/
import Mathlib
import FiniteOrderTM.Basic

namespace PeriodicTM

open Equiv

variable {α : Type*}

namespace Reverser

/-! ### Exponent arithmetic in `Perm α` -/

variable {f : Perm α}

/-- `(f ^ a) r = (f ^ b) r` implies `(f ^ (a - b)) r = r`. -/
theorem zpow_apply_eq_zpow_apply {a b : ℤ} {r : α}
    (h : (f ^ a) r = (f ^ b) r) : (f ^ (a - b)) r = r := by
  have h' := congrArg (f ^ (-b)) h
  calc (f ^ (a - b)) r = (f ^ (-b + a)) r := by rw [neg_add_eq_sub]
    _ = (f ^ (-b)) ((f ^ a) r) := by rw [zpow_add, Perm.mul_apply]
    _ = (f ^ (-b)) ((f ^ b) r) := h'
    _ = (f ^ (-b + b)) r := by rw [zpow_add, Perm.mul_apply]
    _ = r := by rw [neg_add_cancel, zpow_zero, Perm.one_apply]

/-- Transport along a cancellation: from `(f ^ a) r = (f ^ b) r` and
`c + (a - b) = d` conclude `(f ^ c) r = (f ^ d) r`. -/
theorem zpow_apply_eq_of_eq {a b c d : ℤ} {r : α}
    (h : (f ^ a) r = (f ^ b) r) (habcd : c + (a - b) = d) :
    (f ^ c) r = (f ^ d) r := by
  calc (f ^ c) r = (f ^ c) ((f ^ (a - b)) r) := by rw [zpow_apply_eq_zpow_apply h]
    _ = (f ^ (c + (a - b))) r := by rw [zpow_add, Perm.mul_apply]
    _ = (f ^ d) r := by rw [habcd]

/-- `f ((f ^ k) x) = (f ^ (1 + k)) x`. -/
theorem apply_zpow_apply (k : ℤ) (x : α) : f ((f ^ k) x) = (f ^ (1 + k)) x := by
  rw [zpow_add, zpow_one, Perm.mul_apply]

/-- Rewriting the exponent of an applied power. -/
theorem zpow_apply_congr_exp {a b : ℤ} (h : a = b) (x : α) : (f ^ a) x = (f ^ b) x := by
  rw [h]

/-- A power with zero exponent acts trivially. -/
theorem zpow_apply_eq_self_of_exp_zero {k : ℤ} (hk : k = 0) (x : α) : (f ^ k) x = x := by
  rw [hk, zpow_zero, Perm.one_apply]

theorem perm_inv_apply_self (f : Perm α) (x : α) : f⁻¹ (f x) = x :=
  Perm.inv_eq_iff_eq.mpr rfl

theorem perm_apply_inv_self (f : Perm α) (x : α) : f (f⁻¹ x) = x :=
  Perm.eq_inv_iff_eq.mp rfl

/-! ### Orbit data -/

variable (f) in
/-- An *orbit datum* for the permutation `f`: a representative function
`rep`, constant along orbits, and a position function `pos` with
`f ^ pos x (rep x) = x`.  In Theorem 7.3 both are computed from a c.e.
transversal by dovetailing; here they are arbitrary. -/
structure OrbitData where
  rep : α → α
  pos : α → ℤ
  rep_apply : ∀ x, rep (f x) = rep x
  pos_spec : ∀ x, (f ^ pos x) (rep x) = x

variable (D : OrbitData f)

theorem OrbitData.rep_inv_apply (x : α) : D.rep (f⁻¹ x) = D.rep x := by
  have h := D.rep_apply (f⁻¹ x)
  rw [perm_apply_inv_self] at h
  exact h.symm

/-- `rep` is constant along the whole ℤ-orbit. -/
theorem OrbitData.rep_zpow (k : ℤ) : ∀ x, D.rep ((f ^ k) x) = D.rep x := by
  induction k with
  | zero => intro x; simp
  | succ k ih =>
    intro x
    rw [zpow_add_one, Perm.mul_apply, ih, D.rep_apply]
  | pred k ih =>
    intro x
    rw [zpow_sub_one, Perm.mul_apply, ih, D.rep_inv_apply]

theorem OrbitData.rep_eq (x : α) : D.rep x = (f ^ (-D.pos x)) x := by
  have h := D.pos_spec x
  have h' := congrArg (f ^ (-D.pos x)) h
  rw [← Perm.mul_apply, ← zpow_add, neg_add_cancel, zpow_zero, Perm.one_apply] at h'
  exact h'

theorem OrbitData.rep_rep (x : α) : D.rep (D.rep x) = D.rep x := by
  rw [D.rep_eq x, D.rep_zpow]
  exact D.rep_eq x

/-! ### The two reflections -/

/-- Second involution: reflect each orbit about its representative,
`ι₂ x = f ^ (−pos x) (rep x)`. -/
def iota2 (x : α) : α := (f ^ (-D.pos x)) (D.rep x)

/-- First involution: `ι₁ = f ∘ ι₂`. -/
def iota1 (x : α) : α := f (iota2 D x)

theorem rep_iota2 (x : α) : D.rep (iota2 D x) = D.rep x := by
  unfold iota2
  rw [D.rep_zpow, D.rep_rep]

/-- `ι₂` is an involution. -/
theorem iota2_involution : IsInvolution (iota2 D) := by
  intro x
  have hr : D.rep (iota2 D x) = D.rep x := rep_iota2 D x
  -- the position of `ι₂ x` satisfies `f ^ q (rep x) = f ^ (-p) (rep x)`
  have hq : (f ^ D.pos (iota2 D x)) (D.rep x) = (f ^ (-D.pos x)) (D.rep x) := by
    have h := D.pos_spec (iota2 D x)
    rw [hr] at h
    exact h
  show (f ^ (-D.pos (iota2 D x))) (D.rep (iota2 D x)) = x
  rw [hr]
  calc (f ^ (-D.pos (iota2 D x))) (D.rep x) = (f ^ D.pos x) (D.rep x) :=
        zpow_apply_eq_of_eq hq (by ring)
    _ = x := D.pos_spec x

/-- `ι₁` is an involution. -/
theorem iota1_involution : IsInvolution (iota1 D) := by
  intro x
  -- `ι₁ x = f ^ (1 - p) (rep x)`
  have hy : iota1 D x = (f ^ (1 + -D.pos x)) (D.rep x) := by
    unfold iota1 iota2
    rw [apply_zpow_apply]
  have hr : D.rep (iota1 D x) = D.rep x := by
    rw [hy, D.rep_zpow, D.rep_rep]
  have hq : (f ^ D.pos (iota1 D x)) (D.rep x) = (f ^ (1 + -D.pos x)) (D.rep x) := by
    have h := D.pos_spec (iota1 D x)
    rw [hr] at h
    rw [h, hy]
  show f ((f ^ (-D.pos (iota1 D x))) (D.rep (iota1 D x))) = x
  rw [hr, apply_zpow_apply]
  calc (f ^ (1 + -D.pos (iota1 D x))) (D.rep x) = (f ^ D.pos x) (D.rep x) :=
        zpow_apply_eq_of_eq hq (by ring)
    _ = x := D.pos_spec x

/-- The factorisation `f = ι₁ ∘ ι₂`. -/
theorem iota1_iota2 (x : α) : iota1 D (iota2 D x) = f x := by
  show f (iota2 D (iota2 D x)) = f x
  rw [iota2_involution D x]

/-- `ι₂` conjugates `f` to its inverse: `ι₂ ∘ f = f⁻¹ ∘ ι₂` (time symmetry). -/
theorem iota2_reverses (x : α) : iota2 D (f x) = f⁻¹ (iota2 D x) := by
  have h : f (iota2 D (f (iota2 D (iota2 D x)))) = iota2 D x :=
    iota1_involution D (iota2 D x)
  rw [iota2_involution D x] at h
  rw [← h, perm_inv_apply_self]

/-! ### A classical orbit datum for every permutation -/

variable (f) in
/-- The orbit setoid of `f` (the `SameCycle` relation). -/
def orbitSetoid : Setoid α := Perm.SameCycle.setoid f

variable (f) in
/-- Classical representative of the orbit of `x`. -/
noncomputable def classicalRep (x : α) : α :=
  (Quotient.mk (orbitSetoid f) x).out

theorem classicalRep_spec (x : α) : ∃ k : ℤ, (f ^ k) (classicalRep f x) = x :=
  Quotient.exact (s := orbitSetoid f) (Quotient.out_eq _)

theorem classicalRep_apply (x : α) : classicalRep f (f x) = classicalRep f x := by
  unfold classicalRep
  have h : Perm.SameCycle f (f x) x := ⟨-1, by rw [zpow_neg_one, perm_inv_apply_self]⟩
  rw [Quotient.sound (s := orbitSetoid f) h]

variable (f) in
/-- Every permutation admits an orbit datum (classically). -/
noncomputable def classicalOrbitData : OrbitData f where
  rep := classicalRep f
  pos x := Classical.choose (classicalRep_spec (f := f) x)
  rep_apply := classicalRep_apply
  pos_spec x := Classical.choose_spec (classicalRep_spec (f := f) x)

end Reverser

/-! ### Main theorems -/

/-- **Structural core of Theorem 7.3.**  From any orbit datum
(representatives + positions) for a permutation `f`, the explicit
reflections `ι₂ x = f ^ (−pos x) (rep x)` and `ι₁ = f ∘ ι₂` are two
involutions with `ι₁ ∘ ι₂ = f`.  (The effective content of Theorem 7.3 —
that an orbit datum is computable from a c.e. transversal — is not
mechanised.) -/
theorem perm_eq_two_involutions_of_rep (f : Perm α) (D : Reverser.OrbitData f) :
    IsInvolution (Reverser.iota1 D) ∧ IsInvolution (Reverser.iota2 D) ∧
      ∀ x, Reverser.iota1 D (Reverser.iota2 D x) = f x :=
  ⟨Reverser.iota1_involution D, Reverser.iota2_involution D, Reverser.iota1_iota2 D⟩

/-- Every permutation of any type is a product of two involutions
(classical; generalises `exists_two_involutions_of_locallyFinite` to
arbitrary orbits). -/
theorem perm_eq_two_involutions (f : Perm α) :
    ∃ i1 i2 : α → α, IsInvolution i1 ∧ IsInvolution i2 ∧ ∀ x, i1 (i2 x) = f x :=
  let D := Reverser.classicalOrbitData f
  ⟨Reverser.iota1 D, Reverser.iota2 D, Reverser.iota1_involution D,
    Reverser.iota2_involution D, Reverser.iota1_iota2 D⟩

/-- Every permutation is conjugate to its inverse by an involution
(classical strong reversibility). -/
theorem perm_strongly_reversible (f : Perm α) :
    ∃ σ : α → α, IsInvolution σ ∧ ∀ x, σ (f x) = f⁻¹ (σ x) :=
  let D := Reverser.classicalOrbitData f
  ⟨Reverser.iota2 D, Reverser.iota2_involution D, Reverser.iota2_reverses D⟩

end PeriodicTM
