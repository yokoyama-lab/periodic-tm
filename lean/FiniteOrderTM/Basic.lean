/-
FiniteOrderTM/Basic.lean

Effective two-involution decomposition of finite-order bijections
(paper `2026_nakano_rtm`, Theorem `thm:decomp`).

Main result (`finite_order_eq_two_involutions`): on a linearly ordered type,
if `f^[n] = id` pointwise (`OrderDividing n f`, `n ≠ 0`), then `f` factors as
`iota1 ∘ iota2` with both factors involutions. Every construction step is
explicit — orbits are `Finset.range n` images, the basepoint is a `Finset.min'`,
positions are bounded `Nat.find`s — matching the paper's effectivity claim.

The classical algebraic fact (every permutation is a product of two
involutions) is folklore; the content here is that the bound `n` makes the
construction effective. Design notes:

* the orbit is defined as the image of `Finset.range n` (NOT of the minimal
  period), which makes `orbitSet (f x) = orbitSet x` provable without any
  modular arithmetic;
* all exponent arithmetic for the reflections is done in `ZMod m` where
  `m = Function.minimalPeriod f basepoint`; since `m ∣ n` we have `(n : ZMod m)
  = 0` and the dihedral computations reduce to `ring`-style algebra.
-/
import Mathlib

namespace PeriodicTM

open Function

variable {α : Type*} [LinearOrder α]

/-- `f` has order dividing `n`: `f^[n] = id` pointwise. -/
def OrderDividing (n : ℕ) (f : α → α) : Prop := ∀ x, f^[n] x = x

/-- Involution: `f ∘ f = id` pointwise. -/
def IsInvolution (f : α → α) : Prop := ∀ x, f (f x) = x

variable {f : α → α} {n : ℕ}

/-! ### Generalities -/

omit [LinearOrder α] in
theorem injective_of_orderDividing (hn : n ≠ 0) (hf : OrderDividing n f) :
    Function.Injective f := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  intro a b hab
  have ha := hf a
  have hb := hf b
  rw [Function.iterate_succ_apply] at ha hb
  rw [← ha, ← hb, hab]

/-! ### Orbits and basepoints -/

/-- The orbit of `x`, listed as `{x, f x, …, f^[n-1] x}`. -/
def orbitSet (f : α → α) (n : ℕ) (x : α) : Finset α :=
  (Finset.range n).image (fun j => f^[j] x)

theorem mem_orbitSet_self (hn : n ≠ 0) (x : α) : x ∈ orbitSet f n x :=
  Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (Nat.pos_of_ne_zero hn), rfl⟩

theorem orbitSet_nonempty (hn : n ≠ 0) (x : α) : (orbitSet f n x).Nonempty :=
  ⟨x, mem_orbitSet_self hn x⟩

/-- The orbit is invariant under `f` — the payoff of using `range n` instead of
the minimal period: shifting the window `{1, …, n}` back to `{0, …, n-1}` only
needs `f^[n] x = x`, no minimality. -/
theorem orbitSet_apply (hn : n ≠ 0) (hf : OrderDividing n f) (x : α) :
    orbitSet f n (f x) = orbitSet f n x := by
  have hn' : 0 < n := Nat.pos_of_ne_zero hn
  ext y
  simp only [orbitSet, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩
    rcases Nat.lt_or_ge (j + 1) n with h | h
    · exact ⟨j + 1, h, Function.iterate_succ_apply f j x⟩
    · have hjn : j + 1 = n := by omega
      refine ⟨0, hn', ?_⟩
      have : f^[j] (f x) = x := by
        calc f^[j] (f x) = f^[j + 1] x := (Function.iterate_succ_apply f j x).symm
          _ = f^[n] x := by rw [hjn]
          _ = x := hf x
      simp [this]
  · rintro ⟨i, hi, rfl⟩
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · refine ⟨n - 1, by omega, ?_⟩
      have : f^[n - 1] (f x) = f^[n] x := by
        rw [← Function.iterate_succ_apply]
        congr 1
        omega
      simp [this, hf x]
    · refine ⟨i - 1, by omega, ?_⟩
      rw [← Function.iterate_succ_apply]
      congr 1
      omega

theorem orbitSet_iterate (hn : n ≠ 0) (hf : OrderDividing n f) (k : ℕ) (x : α) :
    orbitSet f n (f^[k] x) = orbitSet f n x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', orbitSet_apply hn hf, ih]

variable (f n) in
/-- Canonical basepoint of the orbit of `x`: its minimum. -/
def basepoint [NeZero n] (x : α) : α :=
  (orbitSet f n x).min' (orbitSet_nonempty (NeZero.ne n) x)

theorem basepoint_iterate [NeZero n] (hf : OrderDividing n f) (k : ℕ) (x : α) :
    basepoint f n (f^[k] x) = basepoint f n x := by
  unfold basepoint
  congr 1
  exact orbitSet_iterate (NeZero.ne n) hf k x

theorem basepoint_mem [NeZero n] (x : α) : basepoint f n x ∈ orbitSet f n x :=
  Finset.min'_mem _ _

theorem basepoint_basepoint [NeZero n] (hf : OrderDividing n f) (x : α) :
    basepoint f n (basepoint f n x) = basepoint f n x := by
  obtain ⟨j, _, hb⟩ := Finset.mem_image.mp (basepoint_mem (f := f) (n := n) x)
  rw [← hb, basepoint_iterate hf]
  exact hb.symm

/-! ### Positions along the orbit -/

theorem exists_iterate_basepoint [NeZero n] (hf : OrderDividing n f) (x : α) :
    ∃ p, f^[p] (basepoint f n x) = x := by
  obtain ⟨j, hj, hb⟩ := Finset.mem_image.mp (basepoint_mem (f := f) (n := n) x)
  refine ⟨n - j, ?_⟩
  rw [← hb, ← Function.iterate_add_apply]
  have hjn : n - j + j = n := by
    have := Finset.mem_range.mp hj
    omega
  rw [hjn]
  exact hf x

variable (f n) in
/-- Position of `x` on its orbit: the least `p` with `f^[p] (basepoint x) = x`. -/
def pos [NeZero n] (hf : OrderDividing n f) (x : α) : ℕ :=
  Nat.find (exists_iterate_basepoint hf x)

theorem pos_spec [NeZero n] (hf : OrderDividing n f) (x : α) :
    f^[pos f n hf x] (basepoint f n x) = x :=
  Nat.find_spec (exists_iterate_basepoint hf x)

theorem pos_le [NeZero n] (hf : OrderDividing n f) (x : α) : pos f n hf x ≤ n := by
  obtain ⟨j, hj, hb⟩ := Finset.mem_image.mp (basepoint_mem (f := f) (n := n) x)
  have hwit : f^[n - j] (basepoint f n x) = x := by
    rw [← hb, ← Function.iterate_add_apply]
    have hjn : n - j + j = n := by
      have := Finset.mem_range.mp hj
      omega
    rw [hjn]
    exact hf x
  exact (Nat.find_min' (exists_iterate_basepoint hf x) hwit).trans (Nat.sub_le n j)

/-! ### The congruence criterion at the basepoint -/

/-- Two iterates of the basepoint agree iff their exponents agree modulo the
minimal period. The forward direction reduces both exponents below the minimal
period; the backward direction is iterate-mod reduction. -/
theorem iterate_basepoint_eq_iff [NeZero n] (hf : OrderDividing n f) (x : α)
    {a b : ℕ} :
    f^[a] (basepoint f n x) = f^[b] (basepoint f n x) ↔
      (a : ZMod (minimalPeriod f (basepoint f n x))) = b := by
  set bp := basepoint f n x with hbp
  have hper : IsPeriodicPt f n bp := hf bp
  have hm : 0 < minimalPeriod f bp :=
    hper.minimalPeriod_pos (Nat.pos_of_ne_zero (NeZero.ne n))
  set m := minimalPeriod f bp with hmdef
  rw [ZMod.natCast_eq_natCast_iff]
  constructor
  · intro h
    have ha : f^[a % m] bp = f^[a] bp := iterate_mod_minimalPeriod_eq
    have hb' : f^[b % m] bp = f^[b] bp := iterate_mod_minimalPeriod_eq
    have : f^[a % m] bp = f^[b % m] bp := by rw [ha, hb', h]
    have h1 : a % m < m := Nat.mod_lt _ hm
    have h2 : b % m < m := Nat.mod_lt _ hm
    exact (iterate_eq_iterate_iff_of_lt_minimalPeriod h1 h2).mp this
  · intro h
    have ha : f^[a % m] bp = f^[a] bp := iterate_mod_minimalPeriod_eq
    have hb' : f^[b % m] bp = f^[b] bp := iterate_mod_minimalPeriod_eq
    rw [← ha, ← hb', h]

/-- Position of an explicit iterate of the basepoint, read in `ZMod m`. -/
theorem pos_iterate_basepoint [NeZero n] (hf : OrderDividing n f) (x : α) (k : ℕ) :
    (pos f n hf (f^[k] (basepoint f n x)) :
        ZMod (minimalPeriod f (basepoint f n x))) = k := by
  have hbp : basepoint f n (f^[k] (basepoint f n x)) = basepoint f n x := by
    rw [basepoint_iterate hf, basepoint_basepoint hf]
  have hspec := pos_spec hf (f^[k] (basepoint f n x))
  rw [hbp] at hspec
  exact (iterate_basepoint_eq_iff hf x).mp hspec

/-- `(n : ZMod m) = 0` because the minimal period divides `n`. -/
theorem natCast_n_eq_zero [NeZero n] (hf : OrderDividing n f) (x : α) :
    ((n : ℕ) : ZMod (minimalPeriod f (basepoint f n x))) = 0 := by
  have hper : Function.IsPeriodicPt f n (basepoint f n x) := hf _
  exact (ZMod.natCast_eq_zero_iff _ _).mpr hper.minimalPeriod_dvd

/-! ### The two reflections -/

variable (f n) in
/-- First reflection: reverse the orbit about the basepoint.
`iota2 x = f^[n - pos x] basepoint`, i.e. position `p ↦ -p (mod m)`. -/
def iota2 [NeZero n] (hf : OrderDividing n f) (x : α) : α :=
  f^[n - pos f n hf x] (basepoint f n x)

variable (f n) in
/-- Second reflection: `iota1 = f ∘ iota2`, i.e. position `p ↦ 1 - p (mod m)`. -/
def iota1 [NeZero n] (hf : OrderDividing n f) (x : α) : α :=
  f (iota2 f n hf x)

theorem basepoint_iota2 [NeZero n] (hf : OrderDividing n f) (x : α) :
    basepoint f n (iota2 f n hf x) = basepoint f n x := by
  unfold iota2
  rw [basepoint_iterate hf, basepoint_basepoint hf]

/-- `iota2` is an involution: positions transform as `p ↦ -p ↦ p` in `ZMod m`. -/
theorem iota2_involution [NeZero n] (hf : OrderDividing n f) :
    IsInvolution (iota2 f n hf) := by
  intro x
  set m := minimalPeriod f (basepoint f n x) with hm
  -- the inner point and its data
  have hbp2 : basepoint f n (iota2 f n hf x) = basepoint f n x :=
    basepoint_iota2 hf x
  -- position of `iota2 x` in `ZMod m`
  have hp' : ((pos f n hf (iota2 f n hf x) : ℕ) : ZMod m)
      = ((n - pos f n hf x : ℕ) : ZMod m) := by
    have := pos_iterate_basepoint hf x (n - pos f n hf x)
    simpa [iota2] using this
  -- unfold the outer application and compare exponents at the basepoint
  show f^[n - pos f n hf (iota2 f n hf x)] (basepoint f n (iota2 f n hf x)) = x
  rw [hbp2]
  have hx : f^[pos f n hf x] (basepoint f n x) = x := pos_spec hf x
  conv_rhs => rw [← hx]
  rw [iterate_basepoint_eq_iff hf x, ← hm]
  -- now pure `ZMod m` arithmetic
  have h1 : pos f n hf (iota2 f n hf x) ≤ n := pos_le hf _
  have h2 : pos f n hf x ≤ n := pos_le hf x
  have hn0 : ((n : ℕ) : ZMod m) = 0 := natCast_n_eq_zero hf x
  push_cast [Nat.cast_sub h1, Nat.cast_sub h2] at hp' ⊢
  rw [hp', hn0]
  ring

/-- `iota1` is an involution: positions transform as `p ↦ 1-p ↦ p` in `ZMod m`. -/
theorem iota1_involution [NeZero n] (hf : OrderDividing n f) :
    IsInvolution (iota1 f n hf) := by
  intro x
  set m := minimalPeriod f (basepoint f n x) with hm
  -- `iota1 x` as an explicit iterate of the basepoint
  have hy : iota1 f n hf x
      = f^[(n - pos f n hf x) + 1] (basepoint f n x) := by
    unfold iota1 iota2
    rw [Function.iterate_succ_apply']
  -- basepoint of `iota1 x`
  have hbp1 : basepoint f n (iota1 f n hf x) = basepoint f n x := by
    rw [hy, basepoint_iterate hf, basepoint_basepoint hf]
  -- position of `iota1 x` in `ZMod m`
  have hpy : ((pos f n hf (iota1 f n hf x) : ℕ) : ZMod m)
      = (((n - pos f n hf x) + 1 : ℕ) : ZMod m) := by
    have := pos_iterate_basepoint hf x ((n - pos f n hf x) + 1)
    rw [← hy] at this
    exact this
  -- unfold the outer `iota1` and compare exponents at the basepoint
  show f (iota2 f n hf (iota1 f n hf x)) = x
  have houter : f (iota2 f n hf (iota1 f n hf x))
      = f^[(n - pos f n hf (iota1 f n hf x)) + 1]
          (basepoint f n x) := by
    unfold iota2
    rw [hbp1, Function.iterate_succ_apply']
  rw [houter]
  have hx : f^[pos f n hf x] (basepoint f n x) = x := pos_spec hf x
  conv_rhs => rw [← hx]
  rw [iterate_basepoint_eq_iff hf x, ← hm]
  -- `ZMod m` arithmetic: (n - p_y) + 1 ≡ p, given p_y ≡ (n - p) + 1, n ≡ 0
  have h1 : pos f n hf (iota1 f n hf x) ≤ n := pos_le hf _
  have h2 : pos f n hf x ≤ n := pos_le hf x
  have hn0 : ((n : ℕ) : ZMod m) = 0 := natCast_n_eq_zero hf x
  push_cast [Nat.cast_sub h1, Nat.cast_sub h2] at hpy ⊢
  rw [hpy, hn0]
  ring

/-- The factorisation `f = iota1 ∘ iota2` — NOT definitional: it consumes
`iota2_involution` (the rotation-vs-reflection pitfall caught in the Python
prototype). -/
theorem iota1_iota2 [NeZero n] (hf : OrderDividing n f) (x : α) :
    iota1 f n hf (iota2 f n hf x) = f x := by
  show f (iota2 f n hf (iota2 f n hf x)) = f x
  rw [iota2_involution hf x]

/-! ### Main theorem -/

/-- **Effective decomposition for finite order** (paper Theorem `thm:decomp`):
a bijection of order dividing `n` is the composition of the two explicitly
constructed involutions `iota1` and `iota2`. -/
theorem finite_order_eq_two_involutions [NeZero n] (hf : OrderDividing n f) :
    IsInvolution (iota1 f n hf) ∧ IsInvolution (iota2 f n hf) ∧
      ∀ x, iota1 f n hf (iota2 f n hf x) = f x :=
  ⟨iota1_involution hf, iota2_involution hf, iota1_iota2 hf⟩

/-- Existential corollary, stated without the `NeZero` instance. -/
theorem exists_two_involutions (hn : 0 < n) (hf : OrderDividing n f) :
    ∃ i1 i2 : α → α,
      IsInvolution i1 ∧ IsInvolution i2 ∧ ∀ x, i1 (i2 x) = f x :=
  haveI : NeZero n := ⟨hn.ne'⟩
  ⟨iota1 f n hf, iota2 f n hf,
    iota1_involution hf, iota2_involution hf, iota1_iota2 hf⟩

end PeriodicTM
