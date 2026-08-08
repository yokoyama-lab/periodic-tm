/-
FiniteOrderTM/TwoPointClaimACert.lean

Bounded certificates (`native_decide`) for Claim A of Lemma 9.7
(`FiniteOrderTM/TwoPointClaimA.lean`), matching research/claimA_check.py.

BUILD NOTE.  Like `QueryGame.lean`, this file is deliberately NOT
imported from the root `FiniteOrderTM.lean` (native_decide build cost);
check it with `lake env lean FiniteOrderTM/TwoPointClaimACert.lean`.

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

end PeriodicTM.ClaimA
