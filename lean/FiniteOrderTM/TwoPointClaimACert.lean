/-
FiniteOrderTM/TwoPointClaimACert.lean

Bounded certificates (`native_decide`) for Claim A of Lemma 9.7
(`FiniteOrderTM/TwoPointClaimA.lean`), matching research/claimA_check.py.

BUILD NOTE (corrected 2026-08-21).  This file used to be excluded from
the root `FiniteOrderTM.lean` for build cost, which meant these
certificates never ran in the nightly `lake build` — an unrun check is
indistinguishable from "no problem found".  It is now imported from the
root; the measured one-off cost is 472 s (cached afterwards).

Layer convention: every theorem here is Layer-2 bounded certification
(compiled evaluation); the definitions being evaluated are the
symbolic ones of `TwoPointClaimA.lean`.
-/
import FiniteOrderTM.TwoPointClaimA

namespace PeriodicTM.ClaimA

/-! ## The known counterexample OUTSIDE the region (atomicity)

Research/09 (訂正の経緯): `N = 6`, `ℓ = 4`, two stray paths of one
edge each, no fresh points left.  The formula grants `m = 2`, but the
0-cycle needs 4 vertices = `{0}` + one whole stray path (2 vertices)
+ ONE vertex of the other — impossible, stray paths are atomic. -/

/-- Two one-edge stray paths, nothing walked. -/
def cex : AdvState := ⟨0, 0, [1, 1]⟩

/-- The counterexample state is well-formed for `N = 6` and lies
OUTSIDE the lower-bound region (`q = 2 = min(ℓ−2, k₁*)`).
(`native_decide`, not `decide`: `k1Star` is a `Nat.find`, i.e.
well-founded recursion, which the kernel cannot reduce.) -/
theorem cex_fits_outside :
    cex.Fits 6 ∧ ¬ InLowerRegion 6 4 cex := by native_decide

/-- Formula side says a different-cycle completion should exist
(`m = 2` is a divisor of 4 in the window `[1, 2]`). -/
theorem cex_formula : FormulaSide 6 4 cex := by decide

/-- **Certificate (native_decide):** no different-cycle completion
exists — the formula over-counts outside the region, exactly as the
double-implementation check found. -/
theorem cex_no_completion : ¬ CompletionSide 6 4 cex := by native_decide

/-! ## ALL EIGHT out-of-region counterexamples (completed 2026-08-22)

`research/claimA_check.py --list-outside` enumerates exactly EIGHT
states over the whole sweep (`ℓ ∈ {3,4,5,6}`, `ℓ < N ≤ 10`) where the
formula side and the brute force disagree.  Until 2026-08-22 only the
first one (`cex` above, `N=6, ℓ=4`) was certified here; the other SEVEN
had never been checked by Lean at all, even though the stated goal of
the mechanisation was to check that the known counterexamples come out
FALSE.  They are all certified below.

The eight, as printed by the oracle (every one has
`brute = False, formula = True` — the formula over-counts, it never
under-counts):

    N=6 ℓ=4 k₀=0 k₁=0 strays=[1,1]     ← `cex` above
    N=8 ℓ=6 k₀=0 k₁=0 strays=[1,1,1]
    N=8 ℓ=6 k₀=0 k₁=0 strays=[2,2]
    N=8 ℓ=6 k₀=0 k₁=0 strays=[3,1]
    N=8 ℓ=6 k₀=1 k₁=0 strays=[2,1]
    N=8 ℓ=6 k₀=2 k₁=0 strays=[1,1]
    N=9 ℓ=6 k₀=0 k₁=0 strays=[2,2]
    N=9 ℓ=6 k₀=0 k₁=1 strays=[1,1,1]

Note every one of them has at least TWO stray paths — consistent with
the diagnosis in research/09 that the formula's (⇐) direction ignores
the ATOMICITY of stray paths (a cycle must swallow a stray path whole,
so the formula's vertex budget is too generous).

`¬ CompletionSide` is an exhaustive statement over `Perm (Fin N)`
(`9! = 362880` at `N = 9`), so these are genuine negative results, not
witnesses.  Measured cost when added: ~173 s for the two theorems
together (cached afterwards). -/

/-- **Certificate (native_decide): the five `N = 8` counterexamples.**
Each state fits, lies OUTSIDE the lower-bound region, satisfies the
formula side, and admits NO different-cycle completion. -/
theorem cex_outside_N8_l6 :
    ∀ s ∈ [AdvState.mk 0 0 [1, 1, 1], .mk 0 0 [2, 2], .mk 0 0 [3, 1],
           .mk 1 0 [2, 1], .mk 2 0 [1, 1]],
      s.Fits 8 ∧ ¬ InLowerRegion 8 6 s ∧ FormulaSide 8 6 s ∧
        ¬ CompletionSide 8 6 s := by
  native_decide

/-- **Certificate (native_decide): the two `N = 9` counterexamples.** -/
theorem cex_outside_N9_l6 :
    ∀ s ∈ [AdvState.mk 0 0 [2, 2], .mk 0 1 [1, 1, 1]],
      s.Fits 9 ∧ ¬ InLowerRegion 9 6 s ∧ FormulaSide 9 6 s ∧
        ¬ CompletionSide 9 6 s := by
  native_decide

/-! ## Agreement inside the lower-bound region (spot certificates)

`N = 6, ℓ = 4`: `k₁*(6, 4) = 2`, so the region is `q < 2`.  The states
with `q ≤ 1` are (up to the embedding) `⟨0,0,[]⟩`, `⟨1,0,[]⟩`,
`⟨0,1,[]⟩`, `⟨0,0,[1]⟩`; Claim A asserts both sides hold on each. -/

theorem region_agree_N6_l4 :
    ∀ s ∈ [AdvState.mk 0 0 [], .mk 1 0 [], .mk 0 1 [], .mk 0 0 [1]],
      s.Fits 6 ∧ InLowerRegion 6 4 s ∧
        (FormulaSide 6 4 s ↔ CompletionSide 6 4 s) ∧ CompletionSide 6 4 s := by
  native_decide

/-- `N = 5, ℓ = 3` (the `treeN5` world of QueryGame.lean):
region is `q < 1`, the empty state agrees and completes. -/
theorem region_agree_N5_l3 :
    (AdvState.mk 0 0 []).Fits 5 ∧ InLowerRegion 5 3 (.mk 0 0 []) ∧
      CompletionSide 5 3 (.mk 0 0 []) := by
  native_decide

/-! ## Region sweep: ALL in-region states with N ≤ 8

The enumeration mirrors the python sweep of claimA_check.py
(`stray_partitions`, the `k₀`/`k₁` ranges, the `Fits` skip), and the
state count is cross-checked against the python enumeration: 26 states
for `N ≤ 8` (the full python sweep has 70 for `N ≤ 10`; the
`N ∈ {9, 10}` tail enumerates `Perm (Fin N)` with up to `10! = 3.6M`
elements per state, which wants a backtracking decision procedure
instead of `Fintype` enumeration — left for a later iteration). -/

/-- Partitions as non-increasing part lists with parts `≤ mx` and total
`≤ rest` (python `stray_partitions.gen`), driven by structural fuel so
that the definition is primitive recursive.  `strayPartitions rest mx`
uses `fuel = rest`, which suffices since every part is `≥ 1`. -/
def strayPartitionsF : ℕ → ℕ → ℕ → List (List ℕ)
  | 0, _, _ => [[]]
  | fuel + 1, rest, mx =>
      ([] : List ℕ) ::
        (List.range' 1 (min rest mx)).flatMap fun first =>
          (strayPartitionsF fuel (rest - first) first).map (first :: ·)

def strayPartitions (rest mx : ℕ) : List (List ℕ) :=
  strayPartitionsF rest rest mx

/-- The state list of the python sweep for given `N`, `ℓ`: all
`(k₀, k₁, strays)` with `k₀ + k₁ ≤ ℓ − 2`, stray budget
`ℓ − 2 − k₀ − k₁`, restricted to well-formed (`Fits N`) states in the
lower-bound region. -/
def inRegionStates (N ℓ : ℕ) : List AdvState :=
  ((List.range (ℓ - 1)).flatMap fun k0 =>
    (List.range (ℓ - 1 - k0)).flatMap fun k1 =>
      (strayPartitions (ℓ - 2 - k0 - k1) (ℓ - 2 - k0 - k1)).map
        fun st => AdvState.mk k0 k1 st).filter
    fun s => decide (s.Fits N) && decide (InLowerRegion N ℓ s)

/-- Cross-check of the enumeration against python: exactly 26 in-region
states with `N ≤ 8` (claimA_check.py restricted to `range(l+1, 9)`). -/
theorem region_state_count_N8 :
    (([3, 4, 5, 6] : List ℕ).flatMap fun ℓ =>
      (List.range (8 - ℓ)).flatMap fun d =>
        inRegionStates (ℓ + d + 1) ℓ).length = 26 := by
  native_decide

/-- **Certificate (native_decide): Claim A holds on EVERY in-region
state with `N ≤ 8`** — both sides are TRUE (hence the claimed
equivalence) on all 26 states.  Lean counterpart of python's
`lower-bound region OK=…, BAD=0` for this range, now with the
completion side exhaustive over `Perm (Fin N)` rather than a
backtracking search. -/
theorem region_sweep_N8 :
    ∀ ℓ ∈ ([3, 4, 5, 6] : List ℕ), ∀ d ∈ List.range (8 - ℓ),
      ∀ s ∈ inRegionStates (ℓ + d + 1) ℓ,
        FormulaSide (ℓ + d + 1) ℓ s ∧ CompletionSide (ℓ + d + 1) ℓ s := by
  native_decide

/-! ## Region sweep, N ∈ {9, 10}: witness certificates

At `N ∈ {9, 10}` the exhaustive `∃ f : Perm (Fin N)` check enumerates
up to `10! = 3.6M` permutations per state; instead, since every
in-region state is on the POSITIVE side of Claim A, it suffices to
exhibit one different-cycle completion per state.  The witnesses were
produced by the backtracking search of research/claimA_check.py
(`completions`) and are checked here one permutation each; coverage of
the full enumeration is a separate decidable check, so nothing depends
on the generator having been exhaustive. -/

/-- A permutation from its nontrivial cycles (vertices as `ℕ`, read in
`Fin N` via `Fin.ofNat`): the product of `List.formPerm` of the
cycles.  For genuinely disjoint in-range cycles — the only inputs used
— this is exactly the intended permutation. -/
def ofCycles (N : ℕ) [NeZero N] (cs : List (List ℕ)) : Equiv.Perm (Fin N) :=
  (cs.map fun c => (c.map (Fin.ofNat N)).formPerm).prod

/-- Witness table for `N = 9` (17 in-region states): entries
`(ℓ, state, cycles of a different-cycle completion)`. -/
def witnesses9 : List (ℕ × AdvState × List (List ℕ)) := [
  (3, ⟨0, 0, []⟩, [[0, 2, 3]]),
  (4, ⟨0, 0, []⟩, [[0, 2, 3, 4]]),
  (4, ⟨0, 0, [1]⟩, [[0, 2, 3, 4]]),
  (4, ⟨0, 1, []⟩, [[0, 3, 4, 5], [1, 2]]),
  (4, ⟨1, 0, []⟩, [[0, 2, 3, 4]]),
  (5, ⟨0, 0, []⟩, [[0, 2, 3, 4, 5]]),
  (6, ⟨0, 0, []⟩, [[0, 2, 3, 4, 5, 6]]),
  (6, ⟨0, 0, [1]⟩, [[0, 2, 3, 4, 5, 6]]),
  (6, ⟨0, 0, [1, 1]⟩, [[0, 2, 3, 4, 5, 6]]),
  (6, ⟨0, 0, [2]⟩, [[0, 2, 3, 4, 5, 6]]),
  (6, ⟨0, 1, []⟩, [[0, 3, 4, 5, 6, 7], [1, 2]]),
  (6, ⟨0, 1, [1]⟩, [[0, 3, 4, 5, 6, 7], [1, 2]]),
  (6, ⟨0, 2, []⟩, [[0, 4, 5, 6, 7, 8], [1, 2, 3]]),
  (6, ⟨1, 0, []⟩, [[0, 2, 3, 4, 5, 6]]),
  (6, ⟨1, 0, [1]⟩, [[0, 2, 3, 4, 5, 6]]),
  (6, ⟨1, 1, []⟩, [[0, 2, 4, 5, 6, 7], [1, 3]]),
  (6, ⟨2, 0, []⟩, [[0, 2, 3, 4, 5, 6]])
]

/-- Witness table for `N = 10` (27 in-region states). -/
def witnesses10 : List (ℕ × AdvState × List (List ℕ)) := [
  (3, ⟨0, 0, []⟩, [[0, 2, 3]]),
  (4, ⟨0, 0, []⟩, [[0, 2, 3, 4]]),
  (4, ⟨0, 0, [1]⟩, [[0, 2, 3, 4]]),
  (4, ⟨0, 1, []⟩, [[0, 3, 4, 5], [1, 2]]),
  (4, ⟨1, 0, []⟩, [[0, 2, 3, 4]]),
  (5, ⟨0, 0, []⟩, [[0, 2, 3, 4, 5]]),
  (5, ⟨0, 0, [1]⟩, [[0, 2, 3, 4, 5]]),
  (5, ⟨0, 0, [1, 1]⟩, [[0, 2, 3, 4, 5]]),
  (5, ⟨0, 0, [2]⟩, [[0, 2, 3, 4, 5]]),
  (5, ⟨0, 1, []⟩, [[0, 3, 5, 7, 9], [1, 2, 4, 6, 8]]),
  (5, ⟨0, 1, [1]⟩, [[0, 3, 4, 6, 8], [1, 2, 5, 7, 9]]),
  (5, ⟨0, 2, []⟩, [[0, 4, 6, 8, 9], [1, 2, 3, 5, 7]]),
  (5, ⟨1, 0, []⟩, [[0, 2, 3, 4, 5]]),
  (5, ⟨1, 0, [1]⟩, [[0, 2, 3, 4, 5]]),
  (5, ⟨1, 1, []⟩, [[0, 2, 4, 6, 8], [1, 3, 5, 7, 9]]),
  (5, ⟨2, 0, []⟩, [[0, 2, 3, 4, 5]]),
  (6, ⟨0, 0, []⟩, [[0, 2, 3, 4, 5, 6]]),
  (6, ⟨0, 0, [1]⟩, [[0, 2, 3, 4, 5, 6]]),
  (6, ⟨0, 0, [1, 1]⟩, [[0, 2, 3, 4, 5, 6]]),
  (6, ⟨0, 0, [2]⟩, [[0, 2, 3, 4, 5, 6]]),
  (6, ⟨0, 1, []⟩, [[0, 3, 4, 5, 6, 7], [1, 2]]),
  (6, ⟨0, 1, [1]⟩, [[0, 3, 4, 5, 6, 7], [1, 2]]),
  (6, ⟨0, 2, []⟩, [[0, 4, 5, 6, 7, 8], [1, 2, 3]]),
  (6, ⟨1, 0, []⟩, [[0, 2, 3, 4, 5, 6]]),
  (6, ⟨1, 0, [1]⟩, [[0, 2, 3, 4, 5, 6]]),
  (6, ⟨1, 1, []⟩, [[0, 2, 4, 5, 6, 7], [1, 3]]),
  (6, ⟨2, 0, []⟩, [[0, 2, 3, 4, 5, 6]])
]

/-- Every table witness IS a different-cycle completion of its state. -/
theorem witness_ok_9 :
    ∀ e ∈ witnesses9,
      IsCompletion 9 e.1 e.2.1 (ofCycles 9 e.2.2) ∧
        ¬ (ofCycles 9 e.2.2).SameCycle 0 1 := by native_decide

theorem witness_ok_10 :
    ∀ e ∈ witnesses10,
      IsCompletion 10 e.1 e.2.1 (ofCycles 10 e.2.2) ∧
        ¬ (ofCycles 10 e.2.2).SameCycle 0 1 := by native_decide

/-- The tables COVER the enumeration (and the formula side holds):
every in-region state at `N = 9` / `10` appears with a witness. -/
theorem coverage_9 :
    ∀ ℓ ∈ ([3, 4, 5, 6] : List ℕ), ∀ s ∈ inRegionStates 9 ℓ,
      FormulaSide 9 ℓ s ∧ ∃ e ∈ witnesses9, e.1 = ℓ ∧ e.2.1 = s := by
  native_decide

theorem coverage_10 :
    ∀ ℓ ∈ ([3, 4, 5, 6] : List ℕ), ∀ s ∈ inRegionStates 10 ℓ,
      FormulaSide 10 ℓ s ∧ ∃ e ∈ witnesses10, e.1 = ℓ ∧ e.2.1 = s := by
  native_decide

/-- **Claim A on every in-region state at `N = 9`.** -/
theorem region_sweep_N9 :
    ∀ ℓ ∈ ([3, 4, 5, 6] : List ℕ), ∀ s ∈ inRegionStates 9 ℓ,
      FormulaSide 9 ℓ s ∧ CompletionSide 9 ℓ s := by
  intro ℓ hℓ s hs
  obtain ⟨hf, e, he, hℓe, hse⟩ := coverage_9 ℓ hℓ s hs
  refine ⟨hf, ofCycles 9 e.2.2, ?_, (witness_ok_9 e he).2⟩
  have h := (witness_ok_9 e he).1
  rwa [hℓe, hse] at h

/-- **Claim A on every in-region state at `N = 10`.** -/
theorem region_sweep_N10 :
    ∀ ℓ ∈ ([3, 4, 5, 6] : List ℕ), ∀ s ∈ inRegionStates 10 ℓ,
      FormulaSide 10 ℓ s ∧ CompletionSide 10 ℓ s := by
  intro ℓ hℓ s hs
  obtain ⟨hf, e, he, hℓe, hse⟩ := coverage_10 ℓ hℓ s hs
  refine ⟨hf, ofCycles 10 e.2.2, ?_, (witness_ok_10 e he).2⟩
  have h := (witness_ok_10 e he).1
  rwa [hℓe, hse] at h

/-- Bookend: the full sweep range `N ≤ 10` has exactly 70 in-region
states — the same count as research/claimA_check.py
(`lower-bound region OK=70`).  With `region_sweep_N8` (26 states) and
the witness sweeps at `N = 9` (17) and `N = 10` (27), Claim A is now
machine-checked on ALL of them. -/
theorem region_state_count_N10 :
    (([3, 4, 5, 6] : List ℕ).flatMap fun ℓ =>
      (List.range (10 - ℓ)).flatMap fun d =>
        inRegionStates (ℓ + d + 1) ℓ).length = 70 := by
  native_decide

end PeriodicTM.ClaimA
