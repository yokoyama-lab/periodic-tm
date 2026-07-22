/-
FiniteOrderTM/CopyMultiFold.lean

The per-tape copy fold is semantically reversible.  Split out from `CopyMulti`
because the recursive `SemInverse` proof is compile-heavy: the machines
(`copyStrAt`) carry `selEquiv`/`sumCompl`, so we unfold the recursive `copyPairs`
/ `copyPairsRev` to their `seq` forms with `simp only` *before* applying
`SemInverse.fwd_seq`, keeping the final match syntactic (no deep defeq).
-/
import FiniteOrderTM.CopyMulti

namespace PeriodicTM

open Turing CopyState

variable {Γ : Type*} [Inhabited Γ] [DecidableEq Γ] {ι' : Type*} [DecidableEq ι']

/-- Output domain of the per-tape copy fold: the image of `copyPairs l`. -/
noncomputable def PairsDomOut (l : List {p : ι' × ι' // p.1 ≠ p.2}) :
    (ι' → Tape Γ) → Prop :=
  fun Y => ∃ X, PairsDomIn l X ∧ Y ∈ ktapeSem (copyPairs l) (foldStart l) X

/-- **Forward leg of the fold's semantic inverse.**  On `PairsDomIn l`, the reverse
fold `copyPairsRev l` undoes `copyPairs l`.  List induction: nil = identity; cons =
`fwd_seq` of the head copy (`copyStrAt_semInverse`) and the tail fold (IH), with the
copy-leg precondition discharged by `copyStrAt_preserves_others` + independence. -/
theorem copyPairs_forward {Γ : Type*} [Inhabited Γ] [DecidableEq Γ]
    {ι' : Type*} [DecidableEq ι'] : (l : List {p : ι' × ι' // p.1 ≠ p.2}) →
    ∀ (X Y : ι' → Tape Γ),
    PairsDomIn l X → Y ∈ ktapeSem (copyPairs l) (foldStart l) X →
    X ∈ ktapeSem (copyPairsRev l) (foldStartRev l) Y
  | [] => fun X Y hX hY => (haltMachine_semInverse (PairsDomIn [])).fwd X Y hX hY
  | p :: rest => by
    have h₁fwd : ∀ (X U : ι' → Tape Γ), PairsDomIn (p :: rest) X →
        U ∈ ktapeSem (copyStrAt p.1.1 p.1.2 p.2) CopyState.copy X →
        X ∈ ktapeSem (copyStrAtRev p.1.1 p.1.2 p.2) CopyState.copy U :=
      fun X U hX hU => (copyStrAt_semInverse p.1.1 p.1.2 p.2).fwd X U
        ((copyDomAt_iff p.1.1 p.1.2 p.2 X).mpr hX.1) hU
    have hcompat : ∀ (X U : ι' → Tape Γ), PairsDomIn (p :: rest) X →
        U ∈ ktapeSem (copyStrAt p.1.1 p.1.2 p.2) CopyState.copy X →
        PairsDomIn rest U := by
      intro X U hX hU
      have hpres := copyStrAt_preserves_others p.1.1 p.1.2 p.2 X U
        ((copyDomAt_iff p.1.1 p.1.2 p.2 X).mpr hX.1) hU
      refine (PairsDomIn_congr rest ?_).mpr hX.2.1
      intro q hq
      have hind := hX.2.2 q hq
      exact ⟨hpres q.1.1 (Ne.symm hind.1), hpres q.1.2 (Ne.symm hind.2)⟩
    intro X Y hX hY
    simp only [copyPairs, foldStart] at hY
    simp only [copyPairsRev, foldStartRev]
    exact SemInverse.fwd_seq h₁fwd (copyPairs_forward rest) hcompat X Y hX hY

/-- **The per-tape copy fold is semantically reversible.**  `copyPairsRev l` is a
`SemInverse` of `copyPairs l` on `PairsDomIn l` (each pair's source an anchored
blank-free block, target blank; targets pairwise independent). -/
theorem copyPairs_semInverse {Γ : Type*} [Inhabited Γ] [DecidableEq Γ]
    {ι' : Type*} [DecidableEq ι'] (l : List {p : ι' × ι' // p.1 ≠ p.2}) :
    SemInverse (Γ := Γ) (copyPairs l) (copyPairsRev l) (foldStart l) (foldStartRev l)
      (PairsDomIn l) (PairsDomOut l) where
  fwd := copyPairs_forward l
  bwd := by
    rintro X Y ⟨X₀, hX₀, hYX₀⟩ hXY
    rw [Part.mem_unique hXY (copyPairs_forward l X₀ Y hX₀ hYX₀)]
    exact hYX₀

/-- **The copy fold preserves every bank it does not target.**  Each leg
`copyStrAt p` changes only `p`'s target; banks that are not the target of any pair
in `l` survive the whole fold.  Discharges the `hCompatO` hand-over of the
multi-tape wrapper (the work⊕history block is untouched by the copy). -/
theorem copyPairs_preserves {Γ : Type*} [Inhabited Γ] [DecidableEq Γ]
    {ι' : Type*} [DecidableEq ι'] :
    (l : List {p : ι' × ι' // p.1 ≠ p.2}) → (X V : ι' → Tape Γ) →
    PairsDomIn l X → V ∈ ktapeSem (copyPairs l) (foldStart l) X →
    ∀ b, (∀ p ∈ l, b ≠ p.1.2) → V b = X b
  | [], X, V, _, hV => by
      intro b _
      have hVsome : V ∈ ktapeSem (haltMachine (Γ := Γ) (ι' := ι')) () X := hV
      rw [ktapeSem_haltMachine, Part.mem_some_iff] at hVsome
      rw [hVsome]
  | p :: rest, X, V, hX, hV => by
      intro b hb
      have hbind : V ∈ (ktapeSem (copyStrAt p.1.1 p.1.2 p.2) CopyState.copy X).bind
          (ktapeSem (copyPairs rest) (foldStart rest)) := by
        rw [← ktapeSem_seq]; exact hV
      rw [Part.mem_bind_iff] at hbind
      obtain ⟨W, hW, hVrest⟩ := hbind
      have hWb : W b = X b := copyStrAt_preserves_others p.1.1 p.1.2 p.2 X W
        ((copyDomAt_iff p.1.1 p.1.2 p.2 X).mpr hX.1) hW b (hb p (by simp))
      have hWdom : PairsDomIn rest W := by
        have hpres := copyStrAt_preserves_others p.1.1 p.1.2 p.2 X W
          ((copyDomAt_iff p.1.1 p.1.2 p.2 X).mpr hX.1) hW
        refine (PairsDomIn_congr rest ?_).mpr hX.2.1
        intro q hq
        have hind := hX.2.2 q hq
        exact ⟨hpres q.1.1 (Ne.symm hind.1), hpres q.1.2 (Ne.symm hind.2)⟩
      have hVb : V b = W b :=
        copyPairs_preserves rest W V hWdom hVrest b (fun q hq => hb q (by simp [hq]))
      rw [hVb, hWb]

end PeriodicTM
