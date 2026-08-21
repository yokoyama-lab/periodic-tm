/-
FiniteOrderTM/TwoPointClaimAPack.lean

**The CORRECTED criterion of Claim A (Lemma 9.7).**

`TwoPointClaimA.lean` defines the arithmetic side of Claim A as it is
stated on paper (research/09):

    FormulaSide:  ∃ m ∣ ℓ,  max (k₁+1) (q+r+2−ℓ) ≤ m ≤ N − ℓ

and `TwoPointClaimACert.lean` certifies that this is EQUIVALENT to
`CompletionSide` on every state of the lower-bound region, but WRONG on
exactly eight states outside it (all eight have `FormulaSide` true and
`CompletionSide` false — the formula over-counts, never under-counts).

The diagnosis recorded there is that the term `q+r+2−ℓ` treats the
disclosed vertices as a divisible budget, whereas a stray path of `j`
edges is an ATOMIC block of `j+1` vertices which some ONE cycle must
swallow whole.  This file turns that diagnosis into a criterion.

`PackSide` says: one can choose the length `m ∣ ℓ` of the 1-cycle and
distribute the stray blocks over

  * the 0-cycle (free room `ℓ − (k₀+1)`),
  * the 1-cycle (free room `m − (k₁+1)`),
  * any number of further cycles, each of a length dividing `ℓ`,

so that the padding drawn from the undisclosed points does not exceed
the `N − (q+r+2)` available.  Leftover undisclosed points become fixed
points, which is legitimate because `1 ∣ ℓ`.

Status of the two directions (see research/20-claimA-corrected.md):

  * `pack_side_of_completion` / the converse are NOT proved here.  What
    is machine-checked (in `TwoPointClaimAPackCert.lean`) is that
    `PackSide ↔ CompletionSide` on all bounded states swept so far,
    including the eight states where `FormulaSide` fails, and that the
    python oracle `research/claimA_fixed.py` agrees on 400 states.
  * Theorem 9.6 does NOT depend on this file.  Its lower bound uses
    Claim A only inside the region, where `FormulaSide` is already
    proved correct (`TwoPointClaimAGeneral.lean`).  This file is a
    repair of the *stated* lemma, not a change to the theorem.

Everything here is symbolic (no `native_decide`), so it is safe to
import from the root.
-/
import FiniteOrderTM.TwoPointClaimA

namespace PeriodicTM.ClaimA

/-! ## Divisors, listed in increasing order -/

/-- The divisors of `ℓ` that are `≥ 1`, in increasing order. -/
def divisorsList (ℓ : ℕ) : List ℕ :=
  (List.range (ℓ + 1)).filter fun d => decide (1 ≤ d) && decide (ℓ % d = 0)

/-- The least divisor of `ℓ` that is at least `t` (`none` if there is
none).  Correct because `divisorsList` is increasing. -/
def minDivGE (ℓ t : ℕ) : Option ℕ := (divisorsList ℓ).find? fun d => decide (t ≤ d)

/-! ## Labelings of the stray blocks

Label `0` = the 0-cycle, label `1` = the 1-cycle, labels `2, …, r+1` =
further cycles (at most one per block, which is enough: two blocks in
the same further cycle is the label-sharing case). -/

/-- All lists of length `n` over the labels `0, …, k−1`. -/
def labelings : ℕ → ℕ → List (List ℕ)
  | 0, _ => [[]]
  | n + 1, k => (List.range k).flatMap fun c => (labelings n k).map (c :: ·)

/-- Sum of the entries of `xs` whose label is `c`. -/
def sumLabeled (lbl xs : List ℕ) (c : ℕ) : ℕ :=
  ((lbl.zip xs).filter fun p => decide (p.1 = c)).foldr (fun p acc => p.2 + acc) 0

/-! ## The corrected criterion -/

/-- Padding consumed by the further cycles (labels `2 … r+1`) under the
labeling `lbl`, or `none` if some group has no divisor of `ℓ` large
enough to hold it. -/
def restPad (ℓ : ℕ) (lbl blocks : List ℕ) : Option ℕ :=
  (List.range' 2 blocks.length).foldl
    (fun acc c =>
      match acc with
      | none => none
      | some p =>
          let t := sumLabeled lbl blocks c
          if t = 0 then some p
          else match minDivGE ℓ t with
               | none => none
               | some d => some (p + (d - t)))
    (some 0)

/-- Is the state packable with a 1-cycle of length `m`? -/
def PackWith (N ℓ : ℕ) (s : AdvState) (m : ℕ) : Bool :=
  let blocks := s.strays.map (· + 1)
  let r := blocks.length
  let U := N - s.vertexCount
  decide (s.k0 + 1 ≤ ℓ) && decide (s.k1 + 1 ≤ m) && decide (m ≤ N - ℓ) &&
    decide (s.vertexCount ≤ N) &&
    (labelings r (r + 2)).any fun lbl =>
      let s0 := sumLabeled lbl blocks 0
      let s1 := sumLabeled lbl blocks 1
      decide (s0 ≤ ℓ - (s.k0 + 1)) && decide (s1 ≤ m - (s.k1 + 1)) &&
        match restPad ℓ lbl blocks with
        | none => false
        | some p => decide ((ℓ - (s.k0 + 1) - s0) + (m - (s.k1 + 1) - s1) + p ≤ U)

/-- **Claim A, corrected side.**  Some divisor `m ∣ ℓ` serves as the
length of the 1-cycle and the stray blocks pack, atomically, into the
two cycles and further divisor-length cycles, within the undisclosed
budget. -/
def PackSide (N ℓ : ℕ) (s : AdvState) : Prop :=
  ∃ m ∈ divisorsList ℓ, PackWith N ℓ s m = true

instance (N ℓ : ℕ) (s : AdvState) : Decidable (PackSide N ℓ s) := by
  unfold PackSide; infer_instance

/-! ## Sanity of the auxiliary definitions (symbolic, `decide` only) -/

/-- `divisorsList` really lists divisors, in increasing order. -/
theorem divisorsList_six : divisorsList 6 = [1, 2, 3, 6] := by decide

theorem divisorsList_four : divisorsList 4 = [1, 2, 4] := by decide

/-- `minDivGE` returns the least divisor at or above the threshold. -/
theorem minDivGE_examples :
    minDivGE 6 3 = some 3 ∧ minDivGE 6 4 = some 6 ∧ minDivGE 6 7 = none ∧
      minDivGE 4 3 = some 4 := by
  decide

-- `maxRecDepth`: the kernel builds the 125-element list by structural
-- recursion, which nests deeper than the default 512.  (`set_option … in`
-- must precede the doc comment, like `omit … in`.)
set_option maxRecDepth 8000 in
/-- `labelings` has the expected size: `k ^ n`. -/
theorem labelings_card : (labelings 3 5).length = 125 := by decide

set_option maxRecDepth 8000 in
/-- Every produced labeling has the right length and stays in range. -/
theorem labelings_wf :
    ∀ l ∈ labelings 3 4, l.length = 3 ∧ ∀ c ∈ l, c < 4 := by decide

end PeriodicTM.ClaimA
