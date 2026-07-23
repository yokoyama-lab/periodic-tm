/-
FiniteOrderTM/LocallyFinite.lean

Locally finite decomposition theorem (research notes, Theorem 4.1).

If every point of `f : α → α` is periodic (`LocallyFinite f`, hypothesis (LF)),
then `f` factors as `iota1 ∘ iota2` with both factors involutions. There is no
global bound `n` here, so unlike `Basic.lean` the construction is classical:

* the orbit relation `x ≈ y ↔ ∃ k, f^[k] x = y` is an equivalence — symmetry
  is where (LF) is consumed (running `m - k` further steps around the cycle);
* the basepoint of an orbit is `Quotient.out` of its class (noncomputable);
* positions and reflections then mirror `Basic.lean`, with `n` replaced by the
  orbit-local minimal period `m = minimalPeriod f (rep x)`, and the exponent
  arithmetic done in `ZMod m` where `(m : ZMod m) = 0` holds for free.
-/
import Mathlib
import FiniteOrderTM.Basic

namespace PeriodicTM

open Function

variable {α : Type*} {f : α → α}

attribute [local instance] Classical.propDecidable

/-- Hypothesis (LF): every point is periodic. -/
def LocallyFinite (f : α → α) : Prop := ∀ x, ∃ k, 0 < k ∧ f^[k] x = x

/-- Sanity link to `Basic.lean`: a global order bound gives (LF). -/
theorem locallyFinite_of_orderDividing [LinearOrder α] {n : ℕ} (hn : n ≠ 0)
    (hf : OrderDividing n f) : LocallyFinite f :=
  fun x => ⟨n, Nat.pos_of_ne_zero hn, hf x⟩

namespace LF

/-! ### The orbit relation -/

variable (f) in
/-- Two points are on the same orbit if one is a forward iterate of the other. -/
def OrbitRel (x y : α) : Prop := ∃ k, f^[k] x = y

theorem orbitRel_refl (x : α) : OrbitRel f x x := ⟨0, rfl⟩

theorem orbitRel_trans {x y z : α} (hxy : OrbitRel f x y) (hyz : OrbitRel f y z) :
    OrbitRel f x z := by
  obtain ⟨k, rfl⟩ := hxy
  obtain ⟨l, rfl⟩ := hyz
  exact ⟨l + k, (Function.iterate_add_apply f l k x)⟩

/-- Symmetry of the orbit relation — the step that consumes (LF): to walk back
from `y = f^[k] x` to `x`, walk `m - k % m` further steps around the cycle of
`x`, where `m` is its minimal period. -/
theorem orbitRel_symm (hf : LocallyFinite f) {x y : α} (hxy : OrbitRel f x y) :
    OrbitRel f y x := by
  obtain ⟨k, rfl⟩ := hxy
  obtain ⟨p, hp, hpx⟩ := hf x
  have hper : IsPeriodicPt f p x := hpx
  have hm : 0 < minimalPeriod f x := hper.minimalPeriod_pos hp
  set m := minimalPeriod f x with hmdef
  have hk : f^[k % m] x = f^[k] x := iterate_mod_minimalPeriod_eq
  refine ⟨m - k % m, ?_⟩
  rw [← hk, ← Function.iterate_add_apply]
  have : m - k % m + k % m = m := Nat.sub_add_cancel (Nat.mod_lt _ hm).le
  rw [this]
  exact iterate_minimalPeriod

variable (f) in
/-- The orbit setoid; equivalence needs (LF) for symmetry. -/
def orbitSetoid (hf : LocallyFinite f) : Setoid α :=
  ⟨OrbitRel f, ⟨orbitRel_refl, fun h => orbitRel_symm hf h,
    fun h h' => orbitRel_trans h h'⟩⟩

/-! ### Basepoints (orbit representatives) -/

variable (f) in
/-- Canonical basepoint of the orbit of `x`: `Quotient.out` of its class. -/
noncomputable def rep (hf : LocallyFinite f) (x : α) : α :=
  (Quotient.mk (orbitSetoid f hf) x).out

theorem rep_spec (hf : LocallyFinite f) (x : α) : ∃ k, f^[k] (rep f hf x) = x :=
  Quotient.exact (s := orbitSetoid f hf) (Quotient.out_eq _)

theorem rep_congr (hf : LocallyFinite f) {x y : α} (h : OrbitRel f x y) :
    rep f hf x = rep f hf y := by
  unfold rep
  rw [Quotient.sound (s := orbitSetoid f hf) h]

theorem rep_apply (hf : LocallyFinite f) (x : α) : rep f hf (f x) = rep f hf x :=
  (rep_congr hf ⟨1, rfl⟩).symm

theorem rep_iterate (hf : LocallyFinite f) (k : ℕ) (x : α) :
    rep f hf (f^[k] x) = rep f hf x :=
  (rep_congr hf ⟨k, rfl⟩).symm

theorem rep_rep (hf : LocallyFinite f) (x : α) :
    rep f hf (rep f hf x) = rep f hf x := by
  obtain ⟨k, hk⟩ := rep_spec hf x
  conv_rhs => rw [← hk]
  rw [rep_iterate]

/-! ### Orbit-local period and positions -/

variable (f) in
/-- Length of the orbit of `x`: the minimal period of its basepoint. -/
noncomputable def per (hf : LocallyFinite f) (x : α) : ℕ :=
  minimalPeriod f (rep f hf x)

theorem per_pos (hf : LocallyFinite f) (x : α) : 0 < per f hf x := by
  obtain ⟨k, hk, hkx⟩ := hf (rep f hf x)
  exact (show IsPeriodicPt f k _ from hkx).minimalPeriod_pos hk

theorem iterate_per_rep (hf : LocallyFinite f) (x : α) :
    f^[per f hf x] (rep f hf x) = rep f hf x :=
  iterate_minimalPeriod

variable (f) in
/-- Position of `x` on its orbit: the least `p` with `f^[p] (rep x) = x`. -/
noncomputable def pos (hf : LocallyFinite f) (x : α) : ℕ :=
  Nat.find (rep_spec hf x)

theorem pos_spec (hf : LocallyFinite f) (x : α) :
    f^[pos f hf x] (rep f hf x) = x :=
  Nat.find_spec (rep_spec hf x)

theorem pos_lt (hf : LocallyFinite f) (x : α) : pos f hf x < per f hf x := by
  obtain ⟨k, hk⟩ := rep_spec hf x
  have hm : 0 < per f hf x := per_pos hf x
  have hwit : f^[k % per f hf x] (rep f hf x) = x := by
    rw [per, iterate_mod_minimalPeriod_eq]; exact hk
  exact lt_of_le_of_lt (Nat.find_min' (rep_spec hf x) hwit)
    (Nat.mod_lt _ hm)

/-! ### The congruence criterion at the basepoint -/

/-- Two iterates of the basepoint agree iff their exponents agree in
`ZMod (per x)` — the orbit-local analogue of
`iterate_basepoint_eq_iff` in `Basic.lean`. -/
theorem iterate_rep_eq_iff (hf : LocallyFinite f) (x : α) {a b : ℕ} :
    f^[a] (rep f hf x) = f^[b] (rep f hf x) ↔
      (a : ZMod (per f hf x)) = b := by
  have hm : 0 < per f hf x := per_pos hf x
  set bp := rep f hf x
  set m := per f hf x with hmdef
  rw [ZMod.natCast_eq_natCast_iff]
  constructor
  · intro h
    have ha : f^[a % m] bp = f^[a] bp := iterate_mod_minimalPeriod_eq
    have hb : f^[b % m] bp = f^[b] bp := iterate_mod_minimalPeriod_eq
    have hab : f^[a % m] bp = f^[b % m] bp := by rw [ha, hb, h]
    exact (iterate_eq_iterate_iff_of_lt_minimalPeriod
      (Nat.mod_lt _ hm) (Nat.mod_lt _ hm)).mp hab
  · intro h
    have ha : f^[a % m] bp = f^[a] bp := iterate_mod_minimalPeriod_eq
    have hb : f^[b % m] bp = f^[b] bp := iterate_mod_minimalPeriod_eq
    rw [← ha, ← hb, h]

/-- Position of an explicit iterate of the basepoint, read in `ZMod (per x)`. -/
theorem pos_iterate_rep (hf : LocallyFinite f) (x : α) (k : ℕ) :
    ((pos f hf (f^[k] (rep f hf x)) : ℕ) : ZMod (per f hf x)) = k := by
  have hrep : rep f hf (f^[k] (rep f hf x)) = rep f hf x := by
    rw [rep_iterate, rep_rep]
  have hspec := pos_spec hf (f^[k] (rep f hf x))
  rw [hrep] at hspec
  exact (iterate_rep_eq_iff hf x).mp hspec

/-! ### The two reflections -/

variable (f) in
/-- First reflection: reverse each orbit about its basepoint,
`iota2 x = f^[m - pos x] (rep x)` with `m` the orbit length. -/
noncomputable def iota2 (hf : LocallyFinite f) (x : α) : α :=
  f^[per f hf x - pos f hf x] (rep f hf x)

variable (f) in
/-- Second reflection: `iota1 = f ∘ iota2`. -/
noncomputable def iota1 (hf : LocallyFinite f) (x : α) : α :=
  f (iota2 f hf x)

theorem rep_iota2 (hf : LocallyFinite f) (x : α) :
    rep f hf (iota2 f hf x) = rep f hf x := by
  unfold iota2
  rw [rep_iterate, rep_rep]

theorem per_iota2 (hf : LocallyFinite f) (x : α) :
    per f hf (iota2 f hf x) = per f hf x := by
  unfold per
  rw [rep_iota2]

/-- `iota2` is an involution: positions transform as `p ↦ -p ↦ p` in `ZMod m`. -/
theorem iota2_involution (hf : LocallyFinite f) : IsInvolution (iota2 f hf) := by
  intro x
  set m := per f hf x with hm
  have hrep2 : rep f hf (iota2 f hf x) = rep f hf x := rep_iota2 hf x
  have hper2 : per f hf (iota2 f hf x) = m := per_iota2 hf x
  -- position of `iota2 x` in `ZMod m`
  have hp' : ((pos f hf (iota2 f hf x) : ℕ) : ZMod m)
      = ((m - pos f hf x : ℕ) : ZMod m) := by
    have := pos_iterate_rep hf x (m - pos f hf x)
    simpa [iota2, ← hm] using this
  -- unfold the outer application and compare exponents at the basepoint
  show f^[per f hf (iota2 f hf x) - pos f hf (iota2 f hf x)]
      (rep f hf (iota2 f hf x)) = x
  rw [hrep2, hper2]
  have hx : f^[pos f hf x] (rep f hf x) = x := pos_spec hf x
  conv_rhs => rw [← hx]
  rw [iterate_rep_eq_iff hf x, ← hm]
  -- pure `ZMod m` arithmetic
  have h1 : pos f hf (iota2 f hf x) ≤ m := by
    rw [← hper2]; exact (pos_lt hf _).le
  have h2 : pos f hf x ≤ m := (pos_lt hf x).le
  have hm0 : ((m : ℕ) : ZMod m) = 0 := ZMod.natCast_self m
  push_cast [Nat.cast_sub h1, Nat.cast_sub h2] at hp' ⊢
  rw [hp', hm0]
  ring

/-- `iota1` is an involution: positions transform as `p ↦ 1-p ↦ p` in `ZMod m`. -/
theorem iota1_involution (hf : LocallyFinite f) : IsInvolution (iota1 f hf) := by
  intro x
  set m := per f hf x with hm
  -- `iota1 x` as an explicit iterate of the basepoint
  have hy : iota1 f hf x = f^[(m - pos f hf x) + 1] (rep f hf x) := by
    unfold iota1 iota2
    rw [Function.iterate_succ_apply', ← hm]
  -- basepoint and period of `iota1 x`
  have hrep1 : rep f hf (iota1 f hf x) = rep f hf x := by
    rw [hy, rep_iterate, rep_rep]
  have hper1 : per f hf (iota1 f hf x) = m := by
    rw [hm]; unfold per; rw [hrep1]
  -- position of `iota1 x` in `ZMod m`
  have hpy : ((pos f hf (iota1 f hf x) : ℕ) : ZMod m)
      = (((m - pos f hf x) + 1 : ℕ) : ZMod m) := by
    have := pos_iterate_rep hf x ((m - pos f hf x) + 1)
    rw [← hy, ← hm] at this
    exact this
  -- unfold the outer `iota1` and compare exponents at the basepoint
  show f (iota2 f hf (iota1 f hf x)) = x
  have houter : f (iota2 f hf (iota1 f hf x))
      = f^[(m - pos f hf (iota1 f hf x)) + 1] (rep f hf x) := by
    unfold iota2
    rw [hrep1, hper1, Function.iterate_succ_apply']
  rw [houter]
  have hx : f^[pos f hf x] (rep f hf x) = x := pos_spec hf x
  conv_rhs => rw [← hx]
  rw [iterate_rep_eq_iff hf x, ← hm]
  -- `ZMod m` arithmetic: (m - p_y) + 1 ≡ p, given p_y ≡ (m - p) + 1, m ≡ 0
  have h1 : pos f hf (iota1 f hf x) ≤ m := by
    rw [← hper1]; exact (pos_lt hf _).le
  have h2 : pos f hf x ≤ m := (pos_lt hf x).le
  have hm0 : ((m : ℕ) : ZMod m) = 0 := ZMod.natCast_self m
  push_cast [Nat.cast_sub h1, Nat.cast_sub h2] at hpy ⊢
  rw [hpy, hm0]
  ring

/-- The factorisation `f = iota1 ∘ iota2` — as in `Basic.lean`, it consumes
`iota2_involution`. -/
theorem iota1_iota2 (hf : LocallyFinite f) (x : α) :
    iota1 f hf (iota2 f hf x) = f x := by
  show f (iota2 f hf (iota2 f hf x)) = f x
  rw [iota2_involution hf x]

end LF

/-! ### Main theorem -/

/-- **Locally finite decomposition theorem** (research notes, Theorem 4.1):
if every point of `f` is periodic, `f` is the composition of the two
constructed involutions. -/
theorem locallyFinite_eq_two_involutions (hf : LocallyFinite f) :
    IsInvolution (LF.iota1 f hf) ∧ IsInvolution (LF.iota2 f hf) ∧
      ∀ x, LF.iota1 f hf (LF.iota2 f hf x) = f x :=
  ⟨LF.iota1_involution hf, LF.iota2_involution hf, LF.iota1_iota2 hf⟩

/-- Existential form. -/
theorem exists_two_involutions_of_locallyFinite (hf : LocallyFinite f) :
    ∃ i1 i2 : α → α,
      IsInvolution i1 ∧ IsInvolution i2 ∧ ∀ x, i1 (i2 x) = f x :=
  ⟨LF.iota1 f hf, LF.iota2 f hf,
    LF.iota1_involution hf, LF.iota2_involution hf, LF.iota1_iota2 hf⟩

/-- Corollary re-deriving the `Basic.lean` conclusion through (LF). -/
theorem exists_two_involutions_of_orderDividing [LinearOrder α] {n : ℕ}
    (hn : n ≠ 0) (hf : OrderDividing n f) :
    ∃ i1 i2 : α → α,
      IsInvolution i1 ∧ IsInvolution i2 ∧ ∀ x, i1 (i2 x) = f x :=
  exists_two_involutions_of_locallyFinite (locallyFinite_of_orderDividing hn hf)

end PeriodicTM
