/-
FiniteOrderTM/TwoPointClaimAPackCert.lean

Bounded certificates for the CORRECTED criterion `PackSide`
(`FiniteOrderTM/TwoPointClaimAPack.lean`), and — the point of this file —
a machine-checked demonstration that the formula printed in research/09
is wrong in BOTH directions, not just one.

Until 2026-08-22 the record said the paper formula only ever
OVER-counts: the eight known mismatches all had `FormulaSide` true and
`CompletionSide` false, and `autoresearch/NIGHTLOG.md` stated
「式は過大評価する側にのみ外れ、過小評価は 1 件も無い」.  That statement
was drawn from a sweep bounded by `N ≤ 10`.  It is FALSE at `N = 11`:

    N = 11, ℓ = 6, k₀ = 0, k₁ = 0, strays = [1,1,1,1]

has `FormulaSide` FALSE and yet admits a different-cycle completion
(witness below).  See `formula_undercounts` — this is an UNDER-count,
the direction that would be dangerous if it ever happened inside the
lower-bound region.  (It does not: this state has `q = 4` while
`min (ℓ−2) (k₁*(11,6)) = 3`, so it is outside.  Theorem 9.6 is
untouched; `TwoPointClaimAGeneral.lean` proves the in-region direction
that the theorem actually consumes.)

Layer convention: theorems proved by `decide` are symbolic kernel
evaluation (Layer 1 for a bounded statement); the three marked
`native_decide` are Layer-2 compiled evaluation.  The corrected
criterion `PackSide` is pure arithmetic and IS kernel-decidable — the
two central claims of this file (`pack_kills_overCount`, `under_pack`)
use plain `decide`.  Compiled evaluation is needed only where `k1Star`
(a `Nat.find`) or a permutation of `Fin 11` is involved.
-/
import FiniteOrderTM.TwoPointClaimAPack
import FiniteOrderTM.TwoPointClaimACert

namespace PeriodicTM.ClaimA

/-! ## The eight over-counting states: the corrected criterion kills them -/

/-- The eight states of `research/claimA_check.py --list-outside`, as
`(N, ℓ, state)`. -/
def overCountStates : List (ℕ × ℕ × AdvState) :=
  [(6, 4, ⟨0, 0, [1, 1]⟩),
   (8, 6, ⟨0, 0, [1, 1, 1]⟩), (8, 6, ⟨0, 0, [2, 2]⟩), (8, 6, ⟨0, 0, [3, 1]⟩),
   (8, 6, ⟨1, 0, [2, 1]⟩), (8, 6, ⟨2, 0, [1, 1]⟩),
   (9, 6, ⟨0, 0, [2, 2]⟩), (9, 6, ⟨0, 1, [1, 1, 1]⟩)]

set_option maxRecDepth 100000 in
/-- **On every one of the eight states the paper formula holds but the
corrected criterion does not.**  Symbolic (`decide`): `PackSide` is pure
arithmetic on small lists, so no compiled evaluation is needed. -/
theorem pack_kills_overCount :
    ∀ e ∈ overCountStates,
      FormulaSide e.1 e.2.1 e.2.2 ∧ ¬ PackSide e.1 e.2.1 e.2.2 := by
  decide

/-- Hence on those eight states the corrected criterion AGREES with the
truth, while the formula does not.  The `CompletionSide` half is the
exhaustive `native_decide` result already established in
`TwoPointClaimACert.lean`; nothing is re-evaluated here. -/
theorem pack_agrees_on_cex :
    ¬ PackSide 6 4 cex ∧ ¬ CompletionSide 6 4 cex := by
  refine ⟨?_, cex_no_completion⟩
  have := pack_kills_overCount (6, 4, cex) (by simp [overCountStates, cex])
  exact this.2

/-! ## The ninth state: the formula UNDER-counts (new, 2026-08-22)

`N = 11, ℓ = 6`, four one-edge stray paths.  Disclosed vertices number
`q + r + 2 = 4 + 4 + 2 = 10`, leaving ONE undisclosed point.  The
formula demands a divisor `m ∣ 6` with `max (k₁+1) (q+r+2−ℓ) = 4 ≤ m ≤
N − ℓ = 5`, and `6` has no divisor in `[4,5]`, so `FormulaSide` is
false.  But the term `q+r+2−ℓ` presumes that every disclosed vertex
outside the 0-cycle must live in the 1-cycle, and that is simply not
so: disclosed vertices may sit in FURTHER cycles.  The witness puts two
stray blocks and the spare point into the 0-cycle, leaves `1` as a
fixed point (`m = 1`), and parks the other two stray blocks in two
2-cycles (`2 ∣ 6`):

    (0 2 3 4 5 10)   (1)   (6 7)   (8 9)          6 + 1 + 2 + 2 = 11 -/

def under : AdvState := ⟨0, 0, [1, 1, 1, 1]⟩

/-- The witness permutation, as its nontrivial cycles. -/
def underWitness : Equiv.Perm (Fin 11) :=
  ofCycles 11 [[0, 2, 3, 4, 5, 10], [6, 7], [8, 9]]

/-- The state is well-formed, lies outside the lower-bound region, and
the paper formula says NO different-cycle completion exists. -/
theorem under_fits_outside_formulaFalse :
    under.Fits 11 ∧ ¬ InLowerRegion 11 6 under ∧ ¬ FormulaSide 11 6 under := by
  native_decide

set_option maxRecDepth 100000 in
/-- The corrected criterion says one DOES exist. Symbolic (`decide`). -/
theorem under_pack : PackSide 11 6 under := by decide

/-- **Certificate: the witness really is a different-cycle completion.**
`11! = 39916800`, so this is checked as a witness, not by enumeration —
which is all that is needed, since the claim being refuted is a
NON-existence claim. -/
theorem under_witness_ok :
    IsCompletion 11 6 under underWitness ∧ ¬ underWitness.SameCycle 0 1 := by
  native_decide

/-- **The paper formula under-counts.**  `FormulaSide` is false while a
different-cycle completion exists; the corrected criterion gets it
right.  This is a genuine counterexample in the direction previously
recorded as impossible. -/
theorem formula_undercounts :
    ¬ FormulaSide 11 6 under ∧ CompletionSide 11 6 under ∧
      PackSide 11 6 under :=
  ⟨under_fits_outside_formulaFalse.2.2,
   ⟨underWitness, under_witness_ok.1, under_witness_ok.2⟩,
   under_pack⟩

/-! ## Inside the lower-bound region the corrected criterion still holds

Combined with `region_sweep_N8` / `region_sweep_N9` / `region_sweep_N10`
of `TwoPointClaimACert.lean` (which give `CompletionSide` on exactly
these states), this says `PackSide ↔ CompletionSide` — both true — on
all 70 in-region states of the sweep. -/

/-- `PackSide` holds on every in-region state with `N ≤ 10`.
(`native_decide`, not `decide`: the enumeration `inRegionStates` filters
by `InLowerRegion`, whose `k1Star` is a `Nat.find` that the kernel
cannot reduce — the same reason as `cex_fits_outside`.) -/
theorem pack_region_sweep_N10 :
    ∀ ℓ ∈ ([3, 4, 5, 6] : List ℕ), ∀ d ∈ List.range (10 - ℓ),
      ∀ s ∈ inRegionStates (ℓ + d + 1) ℓ, PackSide (ℓ + d + 1) ℓ s := by
  native_decide

end PeriodicTM.ClaimA
