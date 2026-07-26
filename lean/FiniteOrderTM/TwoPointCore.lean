/-
FiniteOrderTM/TwoPointCore.lean

The general (parametric in `ℓ`, `N`) mathematical core of the two-point
query-game value formula (research/09-two-point-lower-bound.md,
Theorem 9.6: `value(N, ℓ) = min (ℓ − 2) (k₁*(N, ℓ))`).

Contents:
* **Part 1 — Lemma 9.4 (coordinate classification on `ZMod ℓ`).**
  A single ℓ-cycle is modelled abstractly by positions in `ZMod ℓ`,
  reflections by `ρ_c : p ↦ c − p`.  With designated positions
  `pos 0 = 0` and `pos 1 = d`, an output pair `(a, b)` of image
  positions is same-cycle-valid iff `b = a − d`
  (`sameCycleValid_iff`).  The four affine families of output pairs
  (types 1–4 of the table in research/09) are classified: type 3 with
  `β = α` is valid for ALL `d` (`type3_universal`), and validity at
  two values of `d` forces `d₁ = d₂` (types 1, 4), `2d₁ = 2d₂`
  (type 2), or `β = α` (type 3).  The supporting doubling facts
  (`two_mul_injective_of_odd`, `two_mul_succ_ne`) show the type-2
  escape is impossible for odd `ℓ` and for adjacent candidates.
* **Part 2 — Claim B arithmetic and `k₁*`.**
  The strangling-route cost bound `D ≤ ℓ → D ≤ (ℓ + D) / 2` (Claim B
  of research/09; `Nat` floor division, see `claimB_le_half`), the
  least-divisor-≥ function `minDivGe` with its specification, and the
  threshold `k1Star N ℓ` (least `k` such that `ℓ` has no divisor in
  the window `[k+1, N − ℓ]`) with monotonicity in `N` and its
  characterisation through `minDivGe`.
* **Part 3 — reflections on `ZMod ℓ` (bridge preparation).**
  `ρ_c` is an involution, conjugates the rotation `p ↦ p + 1` to its
  inverse, and every map with these two properties is some `ρ_c`
  (`reflection_eq_rho`).  This is the abstract half of the bridge to
  `QueryGame.IsReflection`; the concrete half is listed in the roadmap.

Everything here is symbolic (no `native_decide`), so the file is safe
to import from the root `FiniteOrderTM.lean`.
-/
import Mathlib

namespace PeriodicTM.TwoPointCore

/-! ## Part 1: coordinate classification on a single ℓ-cycle (Lemma 9.4)

Positions on the cycle live in `ZMod ℓ`; the designated points `0` and
`1` of the game sit at positions `0` and `d` (the oriented distance).
A reflection of the cycle is `ρ_c : p ↦ c − p` for some `c : ZMod ℓ`.
An output pair is *same-cycle valid* if it is the image of `(0, d)`
under some reflection. -/

variable {ℓ : ℕ}

/-- The reflection of the ℓ-cycle with parameter `c`, in position
coordinates: `p ↦ c − p`. -/
def rho (c p : ZMod ℓ) : ZMod ℓ := c - p

/-- The output pair `(a, b)` (image positions of the designated points
`0` and `1`, sitting at positions `0` and `d`) is valid for the
same-cycle scenario at distance `d`: some reflection sends `0 ↦ a`
and `d ↦ b`. -/
def SameCycleValid (d a b : ZMod ℓ) : Prop :=
  ∃ c : ZMod ℓ, rho c 0 = a ∧ rho c d = b

/-- **(1a)** The reflection parameter is forced (`c = a`), so validity
is the single linear condition `b = a − d` — the coordinate form of
Lemma 9.4. -/
theorem sameCycleValid_iff (d a b : ZMod ℓ) :
    SameCycleValid d a b ↔ b = a - d := by
  constructor
  · rintro ⟨c, hc0, hcd⟩
    simp only [rho, sub_zero] at hc0
    subst hc0
    simpa [rho] using hcd.symm
  · rintro rfl
    exact ⟨a, by simp [rho], rfl⟩

/-- **(1b)** The type-3 universal family: the pair
`(a, b) = (d + α, α)` (image positions of `f^α(1), f^α(0)`) is valid
for EVERY distance `d`.  For `α = 0` this is the always-valid output
`(1, 0)` of research/09, Observation 9.2. -/
theorem type3_universal (d α : ZMod ℓ) :
    SameCycleValid d (d + α) α := by
  rw [sameCycleValid_iff]
  ring

/-! ### (1c) Completeness: how each affine family behaves under two
distances.  The four types parametrise the output pairs whose two
components are known offsets from the designated points (research/09,
Lemma 9.4 table); `α β : ZMod ℓ` are the constants. -/

/-- Type 1 (`a = α`, `b = β`, both offsets from point `0`): validity at
two distances forces the distances to coincide — the adversary kills
type 1 whenever two candidate distances remain. -/
theorem type1_two_distances (d₁ d₂ α β : ZMod ℓ)
    (h₁ : SameCycleValid d₁ α β) (h₂ : SameCycleValid d₂ α β) :
    d₁ = d₂ := by
  rw [sameCycleValid_iff] at h₁ h₂
  -- h₁ : β = α - d₁, h₂ : β = α - d₂
  linear_combination h₁ - h₂

/-- Type 4 (`a = d + α`, `b = d + β`, both offsets from point `1`):
validity at two distances forces the distances to coincide. -/
theorem type4_two_distances (d₁ d₂ α β : ZMod ℓ)
    (h₁ : SameCycleValid d₁ (d₁ + α) (d₁ + β))
    (h₂ : SameCycleValid d₂ (d₂ + α) (d₂ + β)) :
    d₁ = d₂ := by
  rw [sameCycleValid_iff] at h₁ h₂
  -- h₁ : d₁ + β = d₁ + α - d₁, i.e. β = α - d₁; similarly for d₂.
  have e₁ : β = α - d₁ := by linear_combination h₁
  have e₂ : β = α - d₂ := by linear_combination h₂
  have := e₁.symm.trans e₂
  linear_combination -this

/-- Type 2 (`a = α`, `b = d + β`: `v₀` offset from `0`, `v₁` offset
from `1`): validity at two distances forces `2d₁ = 2d₂`.  Combined
with `two_mul_injective_of_odd` / `two_mul_succ_ne` below, the
adversary kills type 2 whenever two suitable distances remain. -/
theorem type2_two_distances (d₁ d₂ α β : ZMod ℓ)
    (h₁ : SameCycleValid d₁ α (d₁ + β))
    (h₂ : SameCycleValid d₂ α (d₂ + β)) :
    2 * d₁ = 2 * d₂ := by
  rw [sameCycleValid_iff] at h₁ h₂
  -- h₁ : d₁ + β = α - d₁, i.e. 2d₁ = α - β; similarly 2d₂ = α - β.
  linear_combination h₁ - h₂

/-- Type 3 (`a = d + α`, `b = β`: `v₀` offset from `1`, `v₁` offset
from `0`): validity at a SINGLE distance already forces `β = α` — and
then (`type3_universal`) the pair is valid for all distances.  The
distance drops out entirely: type 3 carries no information cost. -/
theorem type3_forces_eq (d α β : ZMod ℓ)
    (h : SameCycleValid d (d + α) β) :
    β = α := by
  rw [sameCycleValid_iff] at h
  linear_combination h

/-! ### (1d) Doubling facts supporting the contiguous-interval argument -/

/-- For odd `ℓ`, doubling is injective on `ZMod ℓ`: `2d₁ = 2d₂ → d₁ = d₂`.
(So for odd `ℓ` the type-2 escape `2d₁ = 2d₂` with `d₁ ≠ d₂` never
happens: "奇数 ℓ は自動".) -/
theorem two_mul_injective_of_odd (hℓ : Odd ℓ) [NeZero ℓ] {d₁ d₂ : ZMod ℓ}
    (h : 2 * d₁ = 2 * d₂) : d₁ = d₂ := by
  have hu : IsUnit (2 : ZMod ℓ) := by
    have : IsUnit ((2 : ℕ) : ZMod ℓ) :=
      (ZMod.isUnit_iff_coprime 2 ℓ).mpr hℓ.coprime_two_left
    simpa using this
  exact hu.mul_left_cancel h

/-- `2 ≠ 0` in `ZMod ℓ` for `ℓ ≥ 3`. -/
theorem two_ne_zero (hℓ : 3 ≤ ℓ) : (2 : ZMod ℓ) ≠ 0 := by
  have : NeZero ℓ := ⟨by omega⟩
  intro h
  have h2 : ((2 : ℕ) : ZMod ℓ) = 0 := by exact_mod_cast h
  have hdvd : ℓ ∣ 2 := (CharP.cast_eq_zero_iff (ZMod ℓ) ℓ 2).mp h2
  have := Nat.le_of_dvd (by norm_num) hdvd
  omega

/-- Adjacent candidate distances have distinct doubles: for `ℓ ≥ 3`
and `d₂ = d₁ + 1` in `ZMod ℓ`, `2d₁ ≠ 2d₂`.  Since the surviving
distance set `D` is a contiguous interval with `|D| ≥ 2`, the
adversary can always pick two candidates whose doubles differ,
whatever the parity of `ℓ`. -/
theorem two_mul_succ_ne (hℓ : 3 ≤ ℓ) (d : ZMod ℓ) :
    2 * d ≠ 2 * (d + 1) := by
  intro h
  apply two_ne_zero hℓ
  linear_combination -h

/-! ## Part 2: Claim B arithmetic and the threshold `k₁*` -/

/-- **Claim B, cost comparison** (research/09 主張B): for naturals with
`D ≤ ℓ`, `D ≤ (ℓ + D) / 2` (floor division).  In the adversary
argument `D = D_max` is the largest divisor of `ℓ` that is `≤ N − ℓ`;
the strangling route costs `q ≥ ⌈(ℓ + D)/2⌉ ≥ (ℓ + D)/2 ≥ D`, so it
is never cheaper than the walking route of cost `D`.  (The statement
with floor division is the weaker rounding, hence implied by and
sufficient for the form used in research/09.) -/
theorem claimB_le_half {D ℓ : ℕ} (h : D ≤ ℓ) : D ≤ (ℓ + D) / 2 := by
  omega

/-- Ceiling variant: `D ≤ (ℓ + D + 1) / 2` follows a fortiori. -/
theorem claimB_le_half_ceil {D ℓ : ℕ} (h : D ≤ ℓ) : D ≤ (ℓ + D + 1) / 2 := by
  omega

/-! ### `minDivGe`: the least divisor of `ℓ` that is `≥ m` -/

/-- Existence of a divisor of `ℓ` that is `≥ m`, provided `m ≤ ℓ`
(then `ℓ` itself qualifies). -/
theorem exists_divisor_ge (hm : m ≤ ℓ) : ∃ k, m ≤ k ∧ k ∣ ℓ :=
  ⟨ℓ, hm, dvd_rfl⟩

/-- `minDivGe ℓ m h` is the least divisor of `ℓ` that is `≥ m`
(research/09: `minDiv(ℓ, m)`), given a witness `h` that one exists
(`exists_divisor_ge` supplies it whenever `m ≤ ℓ`). -/
def minDivGe (ℓ m : ℕ) (h : ∃ k, m ≤ k ∧ k ∣ ℓ) : ℕ := Nat.find h

theorem minDivGe_le' (h : ∃ k, m ≤ k ∧ k ∣ ℓ) : m ≤ minDivGe ℓ m h :=
  (Nat.find_spec h).1

theorem minDivGe_dvd (h : ∃ k, m ≤ k ∧ k ∣ ℓ) : minDivGe ℓ m h ∣ ℓ :=
  (Nat.find_spec h).2

/-- Minimality: `minDivGe` is `≤` any divisor of `ℓ` that is `≥ m`. -/
theorem minDivGe_min (h : ∃ k, m ≤ k ∧ k ∣ ℓ) {k : ℕ}
    (hk : m ≤ k) (hd : k ∣ ℓ) : minDivGe ℓ m h ≤ k :=
  Nat.find_le ⟨hk, hd⟩

/-- In particular `minDivGe ℓ m _ ≤ ℓ` when `m ≤ ℓ`. -/
theorem minDivGe_le_self (hm : m ≤ ℓ) (h : ∃ k, m ≤ k ∧ k ∣ ℓ) :
    minDivGe ℓ m h ≤ ℓ :=
  minDivGe_min h hm dvd_rfl

/-! ### The threshold `k₁*(N, ℓ)`

Research/09 defines `k₁*(N, ℓ) = min { k₁ : minDiv(ℓ, k₁+1) > N − ℓ }`.
We phrase the defining predicate without partiality: `Kills N ℓ k`
says that `ℓ` has NO divisor in the window `[k+1, N − ℓ]` — i.e. the
walking route with `k` steps along the `1`-path already kills every
different-cycle completion. -/

/-- `ℓ` has no divisor `m` with `k + 1 ≤ m ≤ N − ℓ` (all divisors of
`ℓ` are `≤ ℓ`, so the quantifier is bounded and the predicate is
decidable). -/
def Kills (N ℓ k : ℕ) : Prop :=
  ∀ m ≤ ℓ, k + 1 ≤ m → m ∣ ℓ → N - ℓ < m

instance : DecidablePred (Kills N ℓ) := fun _ =>
  inferInstanceAs (Decidable (∀ m ≤ ℓ, _ → _ → _))

/-- `k = ℓ` always kills (vacuously: no divisor of `ℓ` exceeds `ℓ`). -/
theorem kills_exists (N ℓ : ℕ) : ∃ k, Kills N ℓ k :=
  ⟨ℓ, fun _ h₁ h₂ _ => by omega⟩

/-- `k₁*(N, ℓ)`: the least `k` such that `ℓ` has no divisor in
`[k+1, N − ℓ]` (research/09, Theorem 9.6).  Total: it is always
`≤ ℓ`. -/
def k1Star (N ℓ : ℕ) : ℕ := Nat.find (kills_exists N ℓ)

theorem k1Star_kills (N ℓ : ℕ) : Kills N ℓ (k1Star N ℓ) :=
  Nat.find_spec (kills_exists N ℓ)

theorem not_kills_of_lt_k1Star {N ℓ k : ℕ} (h : k < k1Star N ℓ) :
    ¬ Kills N ℓ k :=
  Nat.find_min (kills_exists N ℓ) h

theorem k1Star_le_self (N ℓ : ℕ) : k1Star N ℓ ≤ ℓ :=
  Nat.find_le (fun _ h₁ h₂ _ => by omega)

/-- `Kills` is monotone in `k` (a longer walked path kills at least as
much). -/
theorem Kills.mono {N ℓ k k' : ℕ} (h : Kills N ℓ k) (hk : k ≤ k') :
    Kills N ℓ k' :=
  fun m h₁ h₂ hd => h m h₁ (by omega) hd

/-- `Kills` is antitone in `N` (fewer spare points make killing
easier). -/
theorem Kills.anti {N N' ℓ k : ℕ} (h : Kills N' ℓ k) (hN : N ≤ N') :
    Kills N ℓ k :=
  fun m h₁ h₂ hd => lt_of_le_of_lt (by omega) (h m h₁ h₂ hd)

/-- `k₁*` is monotone in `N`: more spare points can only raise the
threshold. -/
theorem k1Star_mono {N N' : ℕ} (ℓ : ℕ) (hN : N ≤ N') :
    k1Star N ℓ ≤ k1Star N' ℓ :=
  Nat.find_le ((k1Star_kills N' ℓ).anti hN)

/-- Characterisation through `minDivGe`: for `k + 1 ≤ ℓ`, killing is
exactly `minDiv(ℓ, k+1) > N − ℓ` — the form of the definition of
`k₁*` in research/09. -/
theorem kills_iff_minDivGe {N ℓ k : ℕ} (hk : k + 1 ≤ ℓ) :
    Kills N ℓ k ↔ N - ℓ < minDivGe ℓ (k + 1) (exists_divisor_ge hk) := by
  constructor
  · intro h
    exact h _ (minDivGe_le_self hk _) (minDivGe_le' _) (minDivGe_dvd _)
  · intro h m _ h₂ hd
    exact lt_of_lt_of_le h (minDivGe_min _ h₂ hd)

/-! ## Part 3: reflections of `ZMod ℓ` (abstract half of the bridge)

The concrete game (`FiniteOrderTM/QueryGame.lean`) works with
`IsReflection f ι` on `Fin N`.  On a single cycle, in position
coordinates, `f` acts as the rotation `p ↦ p + 1` and a reflection is
characterised by the two equations below; here we prove the abstract
statement that these force `ι = ρ_c` with `c = ι 0`. -/

/-- Every `ρ_c` is an involution. -/
theorem rho_involutive (c : ZMod ℓ) : ∀ p, rho c (rho c p) = p := by
  intro p; simp [rho]

/-- Every `ρ_c` conjugates the rotation `p ↦ p + 1` to its inverse:
`ρ_c (p + 1) = ρ_c p − 1`. -/
theorem rho_conj_rotation (c p : ZMod ℓ) : rho c (p + 1) = rho c p - 1 := by
  simp [rho]; ring

/-- **Rigidity**: any map `ι : ZMod ℓ → ZMod ℓ` that conjugates the
rotation to its inverse (`ι (p + 1) = ι p − 1`) is the reflection
`ρ_{ι 0}`.  (Involutivity is then automatic; it is not even needed as
a hypothesis.)  This is the abstract half of the bridge from
`QueryGame.IsReflection` restricted to one cycle. -/
theorem reflection_eq_rho [NeZero ℓ] (ι : ZMod ℓ → ZMod ℓ)
    (hconj : ∀ p, ι (p + 1) = ι p - 1) :
    ∀ p, ι p = rho (ι 0) p := by
  have key : ∀ n : ℕ, ι (n : ZMod ℓ) = ι 0 - (n : ZMod ℓ) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => push_cast; rw [hconj, ih]; ring
  intro p
  obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective (n := ℓ) p
  simpa [rho] using key n

/-! ## Roadmap to full Theorem 9.6

What remains to formalise the full statement
`value(N, ℓ) = min (ℓ − 2) (k₁*(N, ℓ))` in the `QueryGame` model, and
which lemmas of this file each piece will consume:

1. **Bridge (position isomorphism).**  For `f : Perm (Fin N)` and a
   point `x` on an `f`-cycle of length `ℓ`, build the position map
   `pos : cycle → ZMod ℓ` (`pos (f^i x) = i`) and show that
   `QueryGame.IsReflection f ι`, restricted to the cycle, transports
   to a map satisfying the hypothesis of `reflection_eq_rho`; conclude
   `ι = ρ_c` in coordinates.  Consumes: `reflection_eq_rho`,
   `rho_involutive`, `rho_conj_rotation`.  A useful warm-up special
   case: `f = finRotate ℓ` on `Fin ℓ`, where `pos` is definitionally
   the identity.  Conversely, each `ρ_c` transports back to a valid
   reflection (existence direction, needed for the upper bound).

2. **Transport of Lemma 9.4.**  Via the bridge, `QueryGame.GoodOutput`
   for a same-cycle completion at distance `d` becomes exactly
   `SameCycleValid d a b`; the four-type case analysis of the leaf
   output (each output component is a disclosed offset from `0`/`1`,
   or an undisclosed point) then invokes `type1_two_distances`,
   `type2_two_distances`, `type3_forces_eq`, `type4_two_distances`,
   with `two_mul_injective_of_odd` / `two_mul_succ_ne` discharging the
   type-2 case from two adjacent surviving distances.

3. **Claim A (completion existence).**  Formalise the fresh-answer
   adversary state (paths `P₀`, `P₁`, stray paths) and prove: a
   different-cycle completion exists iff some divisor `m ∣ ℓ`
   satisfies `max (k₁+1) (q+r+2−ℓ) ≤ m ≤ N − ℓ`.  This is a finite
   combinatorial packing argument (place paths on two cycles, fill
   gaps with fresh points).  Consumes: `minDivGe_*` for the divisor
   bookkeeping, and `Kills` / `kills_iff_minDivGe` to phrase
   "different-cycle completion is dead after `k₁` walked steps".

4. **Claim B (adversary cost accounting).**  From Claim A, the two
   ways to kill the different-cycle scenario cost `q ≥ D_max` (walk)
   or `q ≥ (ℓ + D_max)/2` (strangle); `claimB_le_half` shows the
   strangle route is never cheaper, so the minimum kill cost is
   `k1Star N ℓ` (via `k1Star_kills` / `not_kills_of_lt_k1Star`).

5. **Adversary invariant induction over `Tree`.**  Induction on
   `QueryGame.Tree N q` with the invariant "`|D| ≥ 2` (surviving
   distance interval) and a different-cycle completion survives",
   maintained for `q < min (ℓ−2) (k1Star N ℓ)` by the fresh-answer
   strategy; at a leaf, step 2 kills every output pair.  Consumes:
   steps 2–4, `k1Star_mono` (monotonicity in the shrinking budget of
   fresh points), and `Kills.mono`/`Kills.anti`.

6. **Upper bound / assembly.**  Two explicit strategies (walk `k₁*`
   steps from `1`; or pin `d` with `ℓ−2` total steps and output the
   type-2 pair for the pinned `d`) give `value ≤ min (ℓ−2) (k₁*)`;
   with step 5 this yields Theorem 9.6.  The `native_decide`
   certificates of `QueryGame.lean` remain as independent sanity
   checks for small `(N, ℓ)`.
-/

end PeriodicTM.TwoPointCore
