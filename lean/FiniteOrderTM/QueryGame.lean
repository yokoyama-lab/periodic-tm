/-
FiniteOrderTM/QueryGame.lean

Machine-checked certificates for the query-complexity game of
`research/query_lb_search.py` / `research/08-query-experiment.md` ("Game B").

THE GAME.  Fix `N` (domain `Fin N`), `n` (the order: `f ^ n = 1`) and a
promise `ℓ` ("the f-orbit of 0 has length exactly ℓ").  An adaptive
algorithm of depth `q` is a decision tree: each internal node queries a
point `x` and branches on the oracle answer `f x`; each leaf outputs a
pair `(v₀, v₁)`.  The tree WINS if for EVERY permutation `f` with
`f ^ n = 1` satisfying the promise, the leaf reached by running the tree
against `f` outputs a pair `(v₀, v₁)` such that SOME valid
orbit-preserving reflection `ι₂` of `f` (an involution mapping each
`f`-orbit to itself with `f ∘ ι₂` again an involution, i.e. `ι₂`
conjugates `f` to `f⁻¹`) has `ι₂ 0 = v₀` and `ι₂ 1 = v₁`.

TWO-LAYER CONVENTION (as in the rest of the development):
* Layer 1 — general definitions and lemmas, proved once and for all
  (`IsReflection.conj_eq_inv`, `goodOutput_iff_perm`,
  `winnableB_iff_exists_tree`, `winsAt_iff_forall_mem`).  In particular
  `winnableB_iff_exists_tree` shows that the executable minimax check
  `winnableB` is EQUIVALENT to the genuine quantification over ALL
  depth-`q` adaptive decision trees, so the certificates below really do
  quantify over every adaptive strategy.
* Layer 2 — bounded certification by `native_decide` for concrete small
  parameters (clearly marked below).  These match the measured table of
  `research/08-query-experiment.md`:
    - N=5, n=3, ℓ=3:  no depth-0 tree wins, an explicit depth-1 tree
      wins  ⇒  value = 1  (table: q(B) = 1).
    - N=6 and N=7, n=4, ℓ=4:  no depth-1 tree wins, and a depth-2
      strategy exists (N=6)  ⇒  value = 2  (table: q(B) = 2).

BUILD NOTE.  This file is deliberately NOT imported from the root
`FiniteOrderTM.lean`: the `native_decide` certificates take nontrivial
wall-clock time and would slow the default `lake build`.  Check it with
`lake env lean FiniteOrderTM/QueryGame.lean` instead.
-/
import Mathlib

namespace PeriodicTM.QueryGame

open Equiv Finset

variable {N : ℕ}

/-! ## Layer 1: general definitions (arbitrary `N`) -/

/-- `ι` is a *valid orbit-preserving reflection* for `f`: an involution
(`ι ∘ ι = id`), mapping every `f`-orbit into itself
(`∀ x, SameCycle f x (ι x)`), such that `f ∘ ι` is again an involution. -/
def IsReflection (f : Perm (Fin N)) (ι : Fin N → Fin N) : Prop :=
  (∀ x, ι (ι x) = x) ∧ (∀ x, f.SameCycle x (ι x)) ∧ (∀ x, f (ι (f (ι x))) = x)

/-- General lemma: a valid reflection conjugates `f` to `f⁻¹`
(the dihedral time-symmetry; cf. `FiniteOrderTM/Dihedral.lean`). -/
theorem IsReflection.conj_eq_inv {f : Perm (Fin N)} {ι : Fin N → Fin N}
    (h : IsReflection f ι) (x : Fin N) : ι (f (ι x)) = f⁻¹ x := by
  have h3 := h.2.2 x
  have := congrArg (⇑f⁻¹) h3
  simpa using this

/-- The winning condition at a leaf: some single valid reflection takes the
designated points `a`, `b` to the output pair `v₀`, `v₁` (Game B of the
experiment; `a = 0`, `b = 1` below). -/
def GoodOutput (a b : Fin N) (f : Perm (Fin N)) (v₀ v₁ : Fin N) : Prop :=
  ∃ ι : Fin N → Fin N, IsReflection f ι ∧ ι a = v₀ ∧ ι b = v₁

/-- A valid reflection is an involution, hence a bijection; so the search
over all functions can be replaced by a search over permutations (this is
what makes `GoodOutput` efficiently decidable: `N !` candidates instead of
`N ^ N`).  The cheap point-value tests are listed first so that the
compiled decision procedure short-circuits. -/
theorem goodOutput_iff_perm (a b : Fin N) (f : Perm (Fin N)) (v₀ v₁ : Fin N) :
    GoodOutput a b f v₀ v₁ ↔
      ∃ ι : Perm (Fin N), ι a = v₀ ∧ ι b = v₁ ∧ (∀ x, ι (ι x) = x) ∧
        (∀ x, f.SameCycle x (ι x)) ∧ (∀ x, f (ι (f (ι x))) = x) := by
  constructor
  · rintro ⟨ι, ⟨h1, h2, h3⟩, ha, hb⟩
    exact ⟨Function.Involutive.toPerm ι h1, ha, hb, h1, h2, h3⟩
  · rintro ⟨ι, ha, hb, h1, h2, h3⟩
    exact ⟨⇑ι, ⟨h1, h2, h3⟩, ha, hb⟩

instance (a b : Fin N) (f : Perm (Fin N)) (v₀ v₁ : Fin N) :
    Decidable (GoodOutput a b f v₀ v₁) :=
  decidable_of_iff _ (goodOutput_iff_perm a b f v₀ v₁).symm

/-- An adaptive depth-`q` decision tree over the oracle: an internal node
queries a point and branches on the `N` possible answers; a leaf outputs a
pair. -/
inductive Tree (N : ℕ) : ℕ → Type where
  | leaf (v₀ v₁ : Fin N) : Tree N 0
  | node {q : ℕ} (x : Fin N) (child : Fin N → Tree N q) : Tree N (q + 1)

/-- Run the tree against the oracle `f` (at a node querying `x` the oracle
answers `f x`) and demand that the reached leaf is good for `f`. -/
def Runs (a b : Fin N) : {q : ℕ} → Tree N q → Perm (Fin N) → Prop
  | _, .leaf v₀ v₁, f => GoodOutput a b f v₀ v₁
  | _, .node x child, f => Runs a b (child (f x)) f

instance Runs.decidable (a b : Fin N) :
    ∀ {q : ℕ} (t : Tree N q) (f : Perm (Fin N)), Decidable (Runs a b t f)
  | _, .leaf v₀ v₁, f => inferInstanceAs (Decidable (GoodOutput a b f v₀ v₁))
  | _, .node x child, f => Runs.decidable a b (child (f x)) f

/-- The oracle promise: `f ^ n = 1` and the `f`-orbit of `a` has length
exactly `ℓ` (the orbit of `a` is literally the set of points on the same
cycle as `a`, so its `Finset.card` is the orbit length). -/
def Valid (n ℓ : ℕ) (a : Fin N) (f : Perm (Fin N)) : Prop :=
  f ^ n = 1 ∧ #{y | f.SameCycle a y} = ℓ

instance (n ℓ : ℕ) (a : Fin N) (f : Perm (Fin N)) : Decidable (Valid n ℓ a f) :=
  decidable_of_iff ((∀ x, (f ^ n) x = x) ∧ #{y | f.SameCycle a y} = ℓ) <| by
    unfold Valid
    rw [Equiv.ext_iff]
    simp [Perm.one_apply]

/-- The finite set of oracles admitted by the promise. -/
def validPerms (N n ℓ : ℕ) (a : Fin N) : Finset (Perm (Fin N)) :=
  {f | Valid n ℓ a f}

/-- `t` is a winning depth-`q` strategy for the promise `(n, ℓ)` with
designated points `a`, `b`. -/
def WinsAt (n ℓ : ℕ) (a b : Fin N) {q : ℕ} (t : Tree N q) : Prop :=
  ∀ f : Perm (Fin N), Valid n ℓ a f → Runs a b t f

theorem winsAt_iff_forall_mem (n ℓ : ℕ) (a b : Fin N) {q : ℕ} (t : Tree N q) :
    WinsAt n ℓ a b t ↔ ∀ f ∈ validPerms N n ℓ a, Runs a b t f := by
  simp [WinsAt, validPerms]

/-- Executable minimax value check: `winnableB a b q S = true` iff some
depth-`q` adaptive strategy wins against every oracle in `S` (the
equivalence is `winnableB_iff_exists_tree` below).  At depth `q + 1` the
algorithm picks a query `x` and must then win at depth `q` against each
answer-consistent restriction of `S`. -/
def winnableB (a b : Fin N) : ℕ → Finset (Perm (Fin N)) → Bool
  | 0, S => decide (∃ v₀ v₁ : Fin N, ∀ f ∈ S, GoodOutput a b f v₀ v₁)
  | q + 1, S => decide (∃ x : Fin N, ∀ y : Fin N,
      winnableB a b q (S.filter fun f => f x = y) = true)

/-- **Layer-1 key lemma** (general, no `decide`): the executable minimax
check is equivalent to the existence of a winning adaptive decision tree.
This is what makes the `native_decide` certificates below genuine
statements about ALL depth-`q` adaptive strategies. -/
theorem winnableB_iff_exists_tree (a b : Fin N) :
    ∀ (q : ℕ) (S : Finset (Perm (Fin N))),
      winnableB a b q S = true ↔ ∃ t : Tree N q, ∀ f ∈ S, Runs a b t f
  | 0, S => by
    simp only [winnableB, decide_eq_true_eq]
    constructor
    · rintro ⟨v₀, v₁, h⟩
      exact ⟨.leaf v₀ v₁, h⟩
    · rintro ⟨t, h⟩
      cases t with
      | leaf v₀ v₁ => exact ⟨v₀, v₁, h⟩
  | q + 1, S => by
    simp only [winnableB, decide_eq_true_eq]
    constructor
    · rintro ⟨x, hx⟩
      choose g hg using fun y => (winnableB_iff_exists_tree a b q _).mp (hx y)
      refine ⟨.node x g, fun f hf => ?_⟩
      show Runs a b (g (f x)) f
      exact hg (f x) f (mem_filter.mpr ⟨hf, rfl⟩)
    · rintro ⟨t, ht⟩
      cases t with
      | node x child =>
        refine ⟨x, fun y => (winnableB_iff_exists_tree a b q _).mpr
          ⟨child y, fun f hf => ?_⟩⟩
        obtain ⟨hfS, hfx⟩ := mem_filter.mp hf
        have h := ht f hfS
        show Runs a b (child y) f
        rw [← hfx]
        exact h

/-- Convenient contrapositive form for the lower-bound certificates. -/
theorem not_exists_winsAt_of_winnableB_eq_false (n ℓ : ℕ) (a b : Fin N) (q : ℕ)
    (h : winnableB a b q (validPerms N n ℓ a) = false) :
    ¬ ∃ t : Tree N q, WinsAt n ℓ a b t := by
  rintro ⟨t, ht⟩
  rw [winsAt_iff_forall_mem] at ht
  have := (winnableB_iff_exists_tree a b q (validPerms N n ℓ a)).mpr ⟨t, ht⟩
  simp [h] at this

/-! ## Layer 2: `native_decide` certificates (bounded certification)

Every theorem in this section rests on `native_decide` (compiled
evaluation of the decision procedures above); the reduction from
"all adaptive strategies" to the executable check is the *proved*
Layer-1 lemma `winnableB_iff_exists_tree`, so only the evaluation
itself is delegated to the compiler. -/

section N5

/-- **Certificate (native_decide): value ≥ 1 for N = 5, n = 3, ℓ = 3.**
No depth-0 strategy (i.e. no unconditional output pair) wins. -/
theorem no_depth0_N5_n3_l3 : ¬ ∃ t : Tree 5 0, WinsAt 3 3 0 1 t :=
  not_exists_winsAt_of_winnableB_eq_false 3 3 0 1 0 (by native_decide)

/-- An explicit depth-1 winning strategy for N = 5, n = 3, ℓ = 3:
query `0`; if `f 0 = 1` output `(1, 0)`, if `f 0 = c ∉ {0, 1}` output
`(c, 1)` (the branch `f 0 = 0` is unreachable under the promise ℓ = 3). -/
def treeN5 : Tree 5 1 :=
  .node 0 fun y => if y = 1 then .leaf 1 0 else .leaf y 1

/-- **Certificate (native_decide): value ≤ 1 for N = 5, n = 3, ℓ = 3.**
The explicit tree `treeN5` wins against every admissible oracle. -/
theorem treeN5_wins : WinsAt 3 3 0 1 treeN5 := by
  rw [winsAt_iff_forall_mem]
  native_decide

/-- Value = 1 for N = 5, n = 3, ℓ = 3 (matches the measured table). -/
theorem value_eq_one_N5_n3_l3 :
    (¬ ∃ t : Tree 5 0, WinsAt 3 3 0 1 t) ∧ ∃ t : Tree 5 1, WinsAt 3 3 0 1 t :=
  ⟨no_depth0_N5_n3_l3, treeN5, treeN5_wins⟩

end N5

section N6

/-- **Certificate (native_decide): value ≥ 2 for N = 6, n = 4, ℓ = 4.**
No depth-1 adaptive strategy wins. -/
theorem no_depth1_N6_n4_l4 : ¬ ∃ t : Tree 6 1, WinsAt 4 4 0 1 t :=
  not_exists_winsAt_of_winnableB_eq_false 4 4 0 1 1 (by native_decide)

/-- **Certificate (native_decide): value ≤ 2 for N = 6, n = 4, ℓ = 4.**
Some depth-2 adaptive strategy wins (existence via minimax; combined with
the lower bound this pins the value at exactly 2, matching the table). -/
theorem exists_depth2_N6_n4_l4 : ∃ t : Tree 6 2, WinsAt 4 4 0 1 t := by
  simp only [winsAt_iff_forall_mem]
  rw [← winnableB_iff_exists_tree]
  native_decide

end N6

section N7

/-- **Certificate (native_decide): value ≥ 2 for N = 7, n = 4, ℓ = 4.**
No depth-1 adaptive strategy wins. -/
theorem no_depth1_N7_n4_l4 : ¬ ∃ t : Tree 7 1, WinsAt 4 4 0 1 t :=
  not_exists_winsAt_of_winnableB_eq_false 4 4 0 1 1 (by native_decide)

end N7

end PeriodicTM.QueryGame
