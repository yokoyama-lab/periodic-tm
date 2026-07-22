/-
FiniteOrderTM/CopyMultiK.lean

`Fin k` specialization of the per-tape copy fold: copy every work tape `j` onto
ancilla tape `j` on the bank index `(Fin k ⊕ Fin 1) ⊕ Fin k`.  This is
`copyPairs` applied to `List.ofFn (fun j => (work j, ancilla j))`; the pairwise
independence of `PairsDomIn` is automatic because the `Fin k` indices are
distinct, so the input domain collapses to the clean per-tape `MultiDomIn`.
-/
import FiniteOrderTM.CopyMultiFold

namespace PeriodicTM

open Turing CopyState

variable {Γ : Type*} [Inhabited Γ] [DecidableEq Γ]

/-- **General bridge to `PairsDomIn`.**  A pair list satisfies `PairsDomIn` once
each pair has its `CopyDomAt` and the targets are pairwise separated from later
pairs' banks. -/
theorem pairsDomIn_of {ι' : Type*} (X : ι' → Tape Γ) :
    (l : List {p : ι' × ι' // p.1 ≠ p.2}) →
    (∀ p ∈ l, CopyDomAt p.1.1 p.1.2 X) →
    l.Pairwise (fun p q => p.1.2 ≠ q.1.1 ∧ p.1.2 ≠ q.1.2) →
    PairsDomIn l X
  | [], _, _ => trivial
  | p :: rest, hdom, hpw => by
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hpw
    exact ⟨hdom p (by simp),
      pairsDomIn_of X rest (fun q hq => hdom q (by simp [hq])) htail, hhead⟩

/-- The designated pair for tape `j`: copy work bank `inl (inl j)` → ancilla bank
`inr j`. -/
def tapePair (k : ℕ) (j : Fin k) :
    {p : ((Fin k ⊕ Fin 1) ⊕ Fin k) × ((Fin k ⊕ Fin 1) ⊕ Fin k) // p.1 ≠ p.2} :=
  ⟨(Sum.inl (Sum.inl j), Sum.inr j), by simp⟩

/-- The list of all `k` tape pairs. -/
def tapePairs (k : ℕ) : List {p : ((Fin k ⊕ Fin 1) ⊕ Fin k) ×
    ((Fin k ⊕ Fin 1) ⊕ Fin k) // p.1 ≠ p.2} :=
  List.ofFn (tapePair k)

/-- Clean multi-tape input domain: every work tape `j` is an anchored blank-free
block and its ancilla is blank. -/
def MultiDomIn (k : ℕ) (X : ((Fin k ⊕ Fin 1) ⊕ Fin k) → Tape Γ) : Prop :=
  ∀ j : Fin k, CopyDomAt (Sum.inl (Sum.inl j)) (Sum.inr j) X

/-- The `Fin k` pair list satisfies `PairsDomIn` whenever the clean per-tape
`MultiDomIn` holds (independence is automatic from `Fin` distinctness). -/
theorem pairsDomIn_tapePairs (k : ℕ) (X : ((Fin k ⊕ Fin 1) ⊕ Fin k) → Tape Γ)
    (h : MultiDomIn k X) : PairsDomIn (tapePairs k) X := by
  refine pairsDomIn_of X (tapePairs k) ?_ ?_
  · intro p hp
    rw [tapePairs, List.mem_ofFn] at hp
    obtain ⟨j, rfl⟩ := hp
    exact h j
  · rw [tapePairs, List.pairwise_ofFn]
    intro i j hij
    refine ⟨by simp [tapePair], ?_⟩
    simp only [tapePair, ne_eq, Sum.inr.injEq]
    exact (Fin.ne_of_lt hij)

/-- Multi-tape copy on `(Fin k ⊕ Fin 1) ⊕ Fin k`: copy each work tape onto its
ancilla. -/
noncomputable def copyMultiK (k : ℕ) :
    KMachine Γ (FoldState (tapePairs k)) ((Fin k ⊕ Fin 1) ⊕ Fin k) :=
  copyPairs (tapePairs k)

/-- The reverse multi-tape copy. -/
noncomputable def copyMultiKRev (k : ℕ) :
    KMachine Γ (FoldStateRev (tapePairs k)) ((Fin k ⊕ Fin 1) ⊕ Fin k) :=
  copyPairsRev (tapePairs k)

/-- **The multi-tape copy is semantically reversible** on the clean per-tape
domain `MultiDomIn k`. -/
theorem copyMultiK_semInverse (k : ℕ) :
    SemInverse (Γ := Γ) (copyMultiK k) (copyMultiKRev k)
      (foldStart (tapePairs k)) (foldStartRev (tapePairs k))
      (MultiDomIn k) (PairsDomOut (tapePairs k)) :=
  (copyPairs_semInverse (tapePairs k)).mono
    (fun X h => pairsDomIn_tapePairs k X h) (fun _ h => h)

/-- **The multi-tape copy leaves the work⊕history block untouched.**  Every pair's
target is an ancilla bank `Sum.inr j`, so each left bank `Sum.inl b` (a work tape
or the history) survives the copy: `V (Sum.inl b) = X (Sum.inl b)`.  This is the
`hCompatO` hand-over for the multi-tape Bennett wrapper. -/
theorem copyMultiK_preserves_left (k : ℕ)
    (X V : ((Fin k ⊕ Fin 1) ⊕ Fin k) → Tape Γ) (hX : MultiDomIn k X)
    (hV : V ∈ ktapeSem (copyMultiK k) (foldStart (tapePairs k)) X)
    (b : Fin k ⊕ Fin 1) :
    V (Sum.inl b) = X (Sum.inl b) := by
  refine copyPairs_preserves (tapePairs k) X V (pairsDomIn_tapePairs k X hX) hV
    (Sum.inl b) ?_
  intro p hp
  rw [tapePairs, List.mem_ofFn] at hp
  obtain ⟨j, rfl⟩ := hp
  simp [tapePair]

end PeriodicTM
