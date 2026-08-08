/-
FiniteOrderTM/TwoPointClaimA.lean

Claim A of Lemma 9.7 (research/09-two-point-lower-bound.md): for a
fresh-answer adversary state (walked paths `P₀`, `P₁` and stray paths),
a different-cycle completion exists iff some divisor `m ∣ ℓ` satisfies
`max (k₁+1) (q+r+2−ℓ) ≤ m ≤ N − ℓ`.  The equivalence is valid in the
lower-bound region `q < min (ℓ−2) (k₁*)`; outside it the (⇐) direction
over-counts because stray paths are ATOMIC (each must be packed whole
into one cycle) — research/claimA_check.py found 8 counterexamples
there, all with exhausted fresh points.

This file defines BOTH sides as decidable predicates, so that the
bounded equivalence can be machine-checked state by state:

* `FormulaSide`    — the arithmetic (divisor-in-window) condition;
* `CompletionSide` — existence of a genuine different-cycle completion
  of the concretely embedded state (the embedding mirrors
  `research/claimA_check.py`: 0-path on fresh vertices `2, 3, …`, then
  the 1-path, then each stray path from a fresh start vertex).

Everything here is symbolic (no `native_decide`), so the file is safe
to import from the root `FiniteOrderTM.lean`.  The bounded certificates
(agreement on lower-bound-region states, and the known counterexample
`N=6, ℓ=4, strays=[1,1]` outside) live in
`FiniteOrderTM/TwoPointClaimACert.lean`, which — like `QueryGame.lean`
— is NOT imported from the root; check it with
`lake env lean FiniteOrderTM/TwoPointClaimACert.lean`.
-/
import Mathlib
import FiniteOrderTM.TwoPointCore

namespace PeriodicTM.ClaimA

open Equiv Finset

/-! ## The fresh-answer adversary state -/

/-- Fresh-answer adversary state after `q` queries: the disclosed edges
form a path of `k₀` edges from the designated point `0`, a path of `k₁`
edges from `1`, and stray paths of `strays[i] ≥ 1` edges each (paths
never merge nor close under the fresh-answer strategy;
research/09, Lemma 9.7). -/
structure AdvState where
  k0 : ℕ
  k1 : ℕ
  strays : List ℕ
deriving Repr, DecidableEq

namespace AdvState

/-- Total queries answered: every disclosed edge is one query. -/
def q (s : AdvState) : ℕ := s.k0 + s.k1 + s.strays.sum

/-- Number of stray paths. -/
def r (s : AdvState) : ℕ := s.strays.length

/-- Vertices used by the concrete embedding: `0`, `1`, the `k₀ + k₁`
fresh path vertices, and `strays[i] + 1` vertices per stray path. -/
def vertexCount (s : AdvState) : ℕ :=
  2 + s.k0 + s.k1 + s.strays.sum + s.strays.length

/-- The state is well-formed for domain size `N`: stray paths are
nonempty (a stray path of 0 edges is not a path) and the embedding
fits into `Fin N`. -/
def Fits (s : AdvState) (N : ℕ) : Prop :=
  (∀ j ∈ s.strays, 1 ≤ j) ∧ s.vertexCount ≤ N

instance (s : AdvState) (N : ℕ) : Decidable (s.Fits N) := by
  unfold Fits; infer_instance

end AdvState

/-! ## Formula side (the arithmetic of Claim A) -/

/-- Claim A, formula side: some divisor `m ∣ ℓ` lies in the window
`max (k₁+1) (q+r+2−ℓ) ≤ m ≤ N − ℓ` (research/09; `formula` of
claimA_check.py).  The bound `m ∈ range (ℓ+1)` is harmless (every
divisor of `ℓ ≥ 1` is `≤ ℓ`) and makes the predicate decidable. -/
def FormulaSide (N ℓ : ℕ) (s : AdvState) : Prop :=
  ∃ m ∈ Finset.range (ℓ + 1),
    m ∣ ℓ ∧ max (s.k1 + 1) (s.q + s.r + 2 - ℓ) ≤ m ∧ m ≤ N - ℓ

instance (N ℓ : ℕ) (s : AdvState) : Decidable (FormulaSide N ℓ s) := by
  unfold FormulaSide; infer_instance

/-- The formula side is monotone in `N`: extra fresh points can only
help the different-cycle completion. -/
theorem FormulaSide.mono {N N' ℓ : ℕ} {s : AdvState}
    (h : FormulaSide N ℓ s) (hN : N ≤ N') : FormulaSide N' ℓ s := by
  obtain ⟨m, hm, hdvd, hlo, hhi⟩ := h
  exact ⟨m, hm, hdvd, hlo, by omega⟩

/-! ## Completion side (the concrete embedding and its completions) -/

/-- Edges of one disclosed path: start vertex `a`, then `e` fresh
vertices `next, next+1, …, next+e−1` (mirrors `path` of
claimA_check.py). -/
def pathEdges (a next e : ℕ) : List (ℕ × ℕ) :=
  (List.range e).map fun i => (if i = 0 then a else next + i - 1, next + i)

/-- Edges of the stray paths, each starting at a fresh vertex
(mirrors the stray loop of claimA_check.py). -/
def strayEdges : ℕ → List ℕ → List (ℕ × ℕ)
  | _,    [] => []
  | next, j :: rest =>
      pathEdges next (next + 1) j ++ strayEdges (next + 1 + j) rest

/-- The concrete embedding of the whole state as disclosed oracle
edges on `ℕ`: the 0-path uses fresh vertices `2, …`, then the 1-path,
then the stray paths. -/
def AdvState.edges (s : AdvState) : List (ℕ × ℕ) :=
  pathEdges 0 2 s.k0 ++ pathEdges 1 (2 + s.k0) s.k1 ++
    strayEdges (2 + s.k0 + s.k1) s.strays

/-- `f` is a completion of the state: it satisfies the oracle promise
of the two-point game with `n = ℓ` (`f ^ ℓ = 1`, orbit of `0` has
length exactly `ℓ`) and extends every disclosed edge.  The `ℕ`-vertices
of the embedding are read in `Fin N` via `Nat.cast`; for `s.Fits N`
(the only case ever used) all vertices are `< N`, so no wrap-around
occurs. -/
def IsCompletion (N ℓ : ℕ) [NeZero N] (s : AdvState)
    (f : Perm (Fin N)) : Prop :=
  f ^ ℓ = 1 ∧ #{y | f.SameCycle 0 y} = ℓ ∧
    ∀ p ∈ s.edges, f (Fin.ofNat N p.1) = Fin.ofNat N p.2

instance (N ℓ : ℕ) [NeZero N] (s : AdvState) (f : Perm (Fin N)) :
    Decidable (IsCompletion N ℓ s f) :=
  decidable_of_iff
    ((∀ x, (f ^ ℓ) x = x) ∧ #{y | f.SameCycle 0 y} = ℓ ∧
      ∀ p ∈ s.edges, f (Fin.ofNat N p.1) = Fin.ofNat N p.2) <| by
    unfold IsCompletion
    rw [Equiv.ext_iff]
    simp [Perm.one_apply]

/-- Claim A, completion side: a DIFFERENT-CYCLE completion exists —
some admissible oracle extends the disclosed state with `1` outside
the orbit of `0` (`brute` of claimA_check.py, made exhaustive over
`Perm (Fin N)`). -/
def CompletionSide (N ℓ : ℕ) [NeZero N] (s : AdvState) : Prop :=
  ∃ f : Perm (Fin N), IsCompletion N ℓ s f ∧ ¬ f.SameCycle 0 1

instance (N ℓ : ℕ) [NeZero N] (s : AdvState) :
    Decidable (CompletionSide N ℓ s) := by
  unfold CompletionSide; infer_instance

/-! ## The lower-bound region -/

/-- The region in which Claim A is asserted (and used by the
Theorem 9.6 adversary): `q < min (ℓ − 2) (k₁*(N, ℓ))`. -/
def InLowerRegion (N ℓ : ℕ) (s : AdvState) : Prop :=
  s.q < min (ℓ - 2) (PeriodicTM.TwoPointCore.k1Star N ℓ)

instance (N ℓ : ℕ) (s : AdvState) : Decidable (InLowerRegion N ℓ s) := by
  unfold InLowerRegion; infer_instance

/-- **Claim A (statement).**  In the lower-bound region, the two sides
agree.  The bounded instances are certified in
`TwoPointClaimACert.lean`; the general proof (packing argument of
research/09, Lemma 9.7) is the current formalisation target. -/
def Statement (N ℓ : ℕ) [NeZero N] : Prop :=
  ∀ s : AdvState, s.Fits N → InLowerRegion N ℓ s →
    (FormulaSide N ℓ s ↔ CompletionSide N ℓ s)

end PeriodicTM.ClaimA
