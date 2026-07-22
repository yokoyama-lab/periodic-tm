/-
FiniteOrderTM/BennettStrConj.lean

The full-string Bennett conjugation `D = B ; swap ; B'` and its unconditional
symmetrisation, beyond head-valued data.

Unlike the wrapper *reversibility* (`bennettBStr_semInverse_blockdata`,
BennettFCU.lean), which needs only a round-trip, the conjugation needs *exact*
output equality: after the copy the ancilla must hold the entire answer block,
and `B'` must blank it back.  This forces a strictly stronger data predicate than
the reversibility domain: `IsBlock` — a tape blank *outside* a finite prefix
`[0,n)` — the full-string analogue of `IsCell` (blank except at the head).

This file builds, on `IsBlock`, the exact copy-content lemmas the conjugation
needs, starting with tape `nth`-extensionality and the fact that on a block source
the copy's ancilla equals the source.
-/
import FiniteOrderTM.BennettMultiK

namespace PeriodicTM

open Turing

variable {Γ : Type*} [Inhabited Γ] [DecidableEq Γ]

/-- **A block tape.**  Blank-free on the prefix `[0,n)` and blank everywhere else.
This is the data class on which the full-string copy round-trips *exactly* (the
ancilla becomes a full copy of the source, not just a copy on `[0,n)`).  It implies
the copy domain's anchor (`nth (-1) = default`) and block-end (`nth n = default`)
conditions, and is the full-string analogue of `IsCell`. -/
def IsBlock (T : Tape Γ) : Prop :=
  ∃ n : ℕ, (∀ i : ℕ, i < n → T.nth i ≠ default) ∧
    (∀ m : ℤ, ¬(0 ≤ m ∧ m < (n : ℤ)) → T.nth m = default)

/-- **Every single-cell tape is a block** (`n = 0` if the head is blank, else `n = 1`).
So the head-valued data class `IsCell` is contained in the block-data class `IsBlock`:
the full-string symmetrisation domain subsumes the head-valued one. -/
theorem isCell_isBlock {T : Tape Γ} (h : IsCell T) : IsBlock T := by
  by_cases h0 : T.1 = default
  · refine ⟨0, fun i hi => absurd hi (Nat.not_lt_zero i), ?_⟩
    intro m _
    rw [h, h0, Tape.write_nth]
    by_cases hm : m = 0
    · rw [if_pos hm]
    · rw [if_neg hm]; exact Tape.nth_default m
  · refine ⟨1, ?_, ?_⟩
    · intro i hi; interval_cases i; exact h0
    · intro m hm
      have hm0 : m ≠ 0 := by rintro rfl; exact hm ⟨le_refl 0, by norm_num⟩
      rw [h, Tape.write_nth, if_neg hm0]
      exact Tape.nth_default m

/-- **The full-string copy writes the whole source block onto the ancilla.**  On a
block source and a blank target, the unique `copyStr` output's target bank equals
the source bank as a tape (not merely on `[0,n)`): outside the block both are
blank.  Proved by `nth`-extensionality against `copyStr_run_tgt_nth`. -/
theorem copyStr_tgt_eq_src (X V : Unit ⊕ Unit → Tape Γ)
    (hblk : IsBlock (X (Sum.inl ())))
    (htgt : ∀ m : ℤ, (X (Sum.inr ())).nth m = default)
    (hV : V ∈ ktapeSem copyStr CopyState.copy X) :
    V (Sum.inr ()) = X (Sum.inl ()) := by
  obtain ⟨n, hblock, hout⟩ := hblk
  have hanchor : (X (Sum.inl ())).nth (-1) = default := hout (-1) (by omega)
  have hend : (X (Sum.inl ())).nth (n : ℤ) = default := hout (n : ℤ) (by omega)
  have hVeq : V = retTape n ((KStmt.move (fun _ => some Dir.left)).apply (sweepTape n X)) :=
    Part.mem_unique hV (copyStr_output_mem n X hblock hend hanchor)
  apply tape_ext_nth; intro m
  rw [hVeq, copyStr_run_tgt_nth]
  by_cases hc : 0 ≤ m ∧ m < (n : ℤ)
  · rw [if_pos hc]
  · rw [if_neg hc, htgt m]
    exact (hout m hc).symm

/-- **The wrapper-layout copy writes the whole work block onto the ancilla.**
`copyStrW`'s output ancilla `Sum.inr ()` equals the work source
`Sum.inl (Sum.inl ())` on block data.  Transports `copyStr_tgt_eq_src` through
`liftL` (frozen `Fin 1` history) and `renameBank bankEquiv`; the full-string
analogue of `copyWA_anc_full`. -/
theorem copyStrW_anc_full (Y V : (Unit ⊕ Fin 1) ⊕ Unit → Tape Γ)
    (hblk : IsBlock (Y (Sum.inl (Sum.inl ()))))
    (hanc : ∀ m : ℤ, (Y (Sum.inr ())).nth m = default)
    (hV : V ∈ ktapeSem copyStrW CopyState.copy Y) :
    V (Sum.inr ()) = Y (Sum.inl (Sum.inl ())) := by
  rw [copyStrW, ktapeSem_renameBank, Part.mem_map_iff] at hV
  obtain ⟨UL, hUL, rfl⟩ := hV
  obtain ⟨hfrozen, hleft⟩ := ktapeSem_liftL_mem copyStr CopyState.copy hUL
  show UL (bankEquiv.symm (Sum.inr ())) = Y (Sum.inl (Sum.inl ()))
  exact copyStr_tgt_eq_src (fun i => Y (bankEquiv (Sum.inl i))) (UL ∘ Sum.inl)
    hblk hanc hleft

/-- The reverse full-string run output is the value of `copyStrRev`'s tape semantics
(mirror of `copyStr_output_mem`). -/
theorem copyStrRev_output_mem (n : ℕ) (X : Unit ⊕ Unit → Tape Γ)
    (hblock : ∀ i : ℕ, i < n → (X (Sum.inl ())).nth i ≠ default)
    (hend : (X (Sum.inl ())).nth (n : ℤ) = default)
    (hanchor : (X (Sum.inl ())).nth (-1) = default) :
    (retTape n ((KStmt.move (fun _ => some Dir.left)).apply (sweepTapeRev n X)))
      ∈ ktapeSem copyStrRev CopyState.copy X := by
  refine (Part.mem_map_iff _).mpr
    ⟨⟨CopyState.done,
        retTape n ((KStmt.move (fun _ => some Dir.left)).apply (sweepTapeRev n X))⟩, ?_, rfl⟩
  exact StateTransition.mem_eval.mpr
    ⟨copyStrRev_run n X hblock hend hanchor, copyStrRev_step_done _⟩

/-- **The reverse full-string copy blanks the target.**  On a block source (length
`n`) whose target is blank outside `[0,n)`, `copyStrRev` blanks the target bank
entirely: it erases the copy on `[0,n)` and leaves the (already blank) outside.
Proved by `nth`-extensionality against `copyStrRev_run_tgt_nth`. -/
theorem copyStrRev_tgt_blank (X V : Unit ⊕ Unit → Tape Γ) (n : ℕ)
    (hblock : ∀ i : ℕ, i < n → (X (Sum.inl ())).nth i ≠ default)
    (hend : (X (Sum.inl ())).nth (n : ℤ) = default)
    (hanchor : (X (Sum.inl ())).nth (-1) = default)
    (htgtout : ∀ m : ℤ, ¬(0 ≤ m ∧ m < (n : ℤ)) → (X (Sum.inr ())).nth m = default)
    (hV : V ∈ ktapeSem copyStrRev CopyState.copy X) :
    V (Sum.inr ()) = (default : Tape Γ) := by
  have hVeq : V = retTape n ((KStmt.move (fun _ => some Dir.left)).apply (sweepTapeRev n X)) :=
    Part.mem_unique hV (copyStrRev_output_mem n X hblock hend hanchor)
  apply tape_ext_nth; intro m
  rw [hVeq, copyStrRev_run_tgt_nth, Tape.nth_default m]
  by_cases hc : 0 ≤ m ∧ m < (n : ℤ)
  · rw [if_pos hc]
  · rw [if_neg hc]; exact htgtout m hc

/-- **The wrapper-layout reverse copy blanks the ancilla.**  `copyStrWrev`'s output
ancilla `Sum.inr ()` is blank when the work source is a block (length `n`) and the
ancilla is blank outside `[0,n)` (e.g. itself a copy of the block).  Transports
`copyStrRev_tgt_blank` through `liftL` + `renameBank bankEquiv`; the full-string
analogue of `copyWArev_blanks`. -/
theorem copyStrWrev_blanks (Y V : (Unit ⊕ Fin 1) ⊕ Unit → Tape Γ) (n : ℕ)
    (hblock : ∀ i : ℕ, i < n → (Y (Sum.inl (Sum.inl ()))).nth i ≠ default)
    (hend : (Y (Sum.inl (Sum.inl ()))).nth (n : ℤ) = default)
    (hanchor : (Y (Sum.inl (Sum.inl ()))).nth (-1) = default)
    (htgtout : ∀ m : ℤ, ¬(0 ≤ m ∧ m < (n : ℤ)) → (Y (Sum.inr ())).nth m = default)
    (hV : V ∈ ktapeSem copyStrWrev CopyState.copy Y) :
    V (Sum.inr ()) = (default : Tape Γ) := by
  rw [copyStrWrev, ktapeSem_renameBank, Part.mem_map_iff] at hV
  obtain ⟨UL, hUL, rfl⟩ := hV
  obtain ⟨hfrozen, hleft⟩ := ktapeSem_liftL_mem copyStrRev CopyState.copy hUL
  show UL (bankEquiv.symm (Sum.inr ())) = (default : Tape Γ)
  exact copyStrRev_tgt_blank (fun i => Y (bankEquiv (Sum.inl i))) (UL ∘ Sum.inl) n
    hblock hend hanchor htgtout hleft

/-! ### Wrapper correctness on block data (conj-3) -/

variable {Λ : Type*} [DecidableEq Λ]

/-- `IsBlock` is preserved by lifting into the Bennett alphabet (`Tape.map inlMap`
acts cellwise, and `default = Sum.inl default`).  Full-string analogue of
`isCell_map`. -/
theorem isBlock_map {ι : Type*} {T : Tape Γ} (h : IsBlock T) :
    IsBlock (Tape.map (inlMap : PointedMap Γ (BennettAlph2 Γ Λ ι)) T) := by
  obtain ⟨n, hblock, hout⟩ := h
  refine ⟨n, ?_, ?_⟩
  · intro i hi hc
    rw [Tape.map_nth] at hc
    have h2 : (Sum.inl (T.nth (i : ℤ)) : BennettAlph2 Γ Λ ι) = Sum.inl default := hc
    exact hblock i hi (Sum.inl.inj h2)
  · intro m hm
    rw [Tape.map_nth]
    exact congrArg Sum.inl (hout m hm)

/-- A block source with a blank ancilla meets the wrapper copy's `CopyDomIn`. -/
theorem isBlock_copyDomIn (Y : (Unit ⊕ Fin 1) ⊕ Unit → Tape Γ)
    (hblk : IsBlock (Y (Sum.inl (Sum.inl ()))))
    (hanc : ∀ m : ℤ, (Y (Sum.inr ())).nth m = default) :
    CopyDomIn (fun i => Y (bankEquiv (Sum.inl i))) := by
  obtain ⟨n, hblock, hout⟩ := hblk
  exact ⟨hout (-1) (by omega), hanc, n, hblock, hout (n : ℤ) (by omega)⟩

/-- **The wrapper copy halts on block data.**  A member of `copyStrW`'s tape
semantics exists whenever the work source is a block.  Built by transporting
`copyStr_output_mem` through `liftL` and `renameBank bankEquiv`. -/
theorem copyStrW_output_exists (Y : (Unit ⊕ Fin 1) ⊕ Unit → Tape Γ)
    (hblk : IsBlock (Y (Sum.inl (Sum.inl ())))) :
    ∃ W, W ∈ ktapeSem copyStrW CopyState.copy Y := by
  obtain ⟨n, hblock, hout⟩ := hblk
  rw [copyStrW, ktapeSem_renameBank,
    show (fun i => Y (bankEquiv i))
        = withR ((fun i => Y (bankEquiv i)) ∘ Sum.inr) (fun i => Y (bankEquiv (Sum.inl i))) from
        (Sum.elim_comp_inl_inr (fun i => Y (bankEquiv i))).symm,
    ktapeSem_liftL]
  exact ⟨_, (Part.mem_map_iff _).mpr ⟨_, (Part.mem_map_iff _).mpr
    ⟨_, copyStr_output_mem n (fun i => Y (bankEquiv (Sum.inl i))) hblock
      (hout (n : ℤ) (by omega)) (hout (-1) (by omega)), rfl⟩, rfl⟩⟩

/-- **Exact `bennettBStr` output on block data.**  Full-string analogue of
`bennettB_correct_full`: when `M₀` maps `A` to a *block* `U`, the work⊕history block
is restored to `liftWork A` and the ancilla holds `liftWork U` exactly (the whole
answer block, not just its head).  The copy now fills the ancilla with the entire
source block (`copyStrW_anc_full`), so no `cell_lift` is needed. -/
theorem bennettBStr_correct_full (M₀ : KMachine Γ Λ Unit) (q₀ : Λ) (A U : Unit → Tape Γ)
    (hU : ∀ j, IsBlock (U j)) (hAU : U ∈ ktapeSem M₀ q₀ A) :
    withR (fun j => liftWork M₀ U (Sum.inl j)) (liftWork M₀ A)
      ∈ ktapeSem (bennettBStr M₀) (Sum.inl (Sum.inl (BennettState2.A1 q₀)))
          (withR (fun _ : Unit => (default : Tape (BennettAlph2 Γ Λ Unit)))
            (liftWork M₀ A)) := by
  classical
  obtain ⟨Y, hY, hYwork⟩ := phaseF2_forward_correct M₀ q₀ A U hAU
  set Uf : (Unit ⊕ Fin 1) ⊕ Unit → Tape (BennettAlph2 Γ Λ Unit) :=
    withR (fun _ : Unit => (default : Tape (BennettAlph2 Γ Λ Unit))) Y with hUf
  have hUfmem : Uf ∈ ktapeSem (liftL (phaseF2 M₀) (κ := Unit)) (BennettState2.A1 q₀)
      (withR (fun _ : Unit => (default : Tape (BennettAlph2 Γ Λ Unit))) (liftWork M₀ A)) := by
    rw [ktapeSem_liftL, Part.mem_map_iff]; exact ⟨Y, hY, rfl⟩
  have hblkUf : IsBlock (Uf (Sum.inl (Sum.inl ()))) := by
    show IsBlock (Y (Sum.inl ()))
    rw [hYwork ()]; exact isBlock_map (hU ())
  have hancUf : ∀ m : ℤ, (Uf (Sum.inr ())).nth m = default := by
    intro m; show ((default : Tape (BennettAlph2 Γ Λ Unit))).nth m = default
    exact Tape.nth_default m
  obtain ⟨W, hWmem⟩ := copyStrW_output_exists Uf hblkUf
  have hWinlY : W ∘ Sum.inl = Y := by
    funext x; show W (Sum.inl x) = Y x
    rw [copyStrW_preserves_left Uf W (isBlock_copyDomIn Uf hblkUf hancUf) hWmem x]; rfl
  have hWinrEq : W ∘ Sum.inr = fun j => liftWork M₀ U (Sum.inl j) := by
    funext j; cases j
    show W (Sum.inr ()) = liftWork M₀ U (Sum.inl ())
    rw [copyStrW_anc_full Uf W hblkUf hancUf hWmem]
    show Y (Sum.inl ()) = liftWork M₀ U (Sum.inl ())
    exact hYwork ()
  have hUuncompute : liftWork M₀ A ∈
      ktapeSem (phaseU2 M₀) UncompState.RStart (W ∘ Sum.inl) := by
    rw [hWinlY]
    exact (phaseF2_semInverse M₀ q₀).fwd (liftWork M₀ A) Y (liftWork_WFblank M₀ A) hY
  rw [bennettBStr, ktapeSem_seq, Part.mem_bind_iff]
  refine ⟨W, ?_, ?_⟩
  · rw [ktapeSem_seq, Part.mem_bind_iff]
    exact ⟨Uf, hUfmem, hWmem⟩
  · rw [show W = withR (W ∘ Sum.inr) (W ∘ Sum.inl) from (Sum.elim_comp_inl_inr W).symm,
        ktapeSem_liftL, Part.mem_map_iff]
    refine ⟨liftWork M₀ A, hUuncompute, ?_⟩
    rw [hWinrEq]

/-! ### Reverse leg correctness on block data (conj-3b) -/

/-- **The reverse full-string copy preserves the source bank.**  Mirror of
`copyStr_preserves_src` for `copyStrRev`, via `copyStrRev_output_mem` +
`copyStrRev_run_src`. -/
theorem copyStrRev_preserves_src (X V : Unit ⊕ Unit → Tape Γ) (n : ℕ)
    (hblock : ∀ i : ℕ, i < n → (X (Sum.inl ())).nth i ≠ default)
    (hend : (X (Sum.inl ())).nth (n : ℤ) = default)
    (hanchor : (X (Sum.inl ())).nth (-1) = default)
    (hV : V ∈ ktapeSem copyStrRev CopyState.copy X) :
    V (Sum.inl ()) = X (Sum.inl ()) := by
  have hVeq : V = retTape n ((KStmt.move (fun _ => some Dir.left)).apply (sweepTapeRev n X)) :=
    Part.mem_unique hV (copyStrRev_output_mem n X hblock hend hanchor)
  rw [hVeq]; exact copyStrRev_run_src n X

/-- **The wrapper-layout reverse copy preserves the work⊕history banks.**  Mirror of
`copyStrW_preserves_left` for `copyStrWrev` (source via `copyStrRev_preserves_src`,
frozen `Fin 1` ancilla via `liftL`). -/
theorem copyStrWrev_preserves_left (Y V : (Unit ⊕ Fin 1) ⊕ Unit → Tape Γ) (n : ℕ)
    (hblock : ∀ i : ℕ, i < n → (Y (Sum.inl (Sum.inl ()))).nth i ≠ default)
    (hend : (Y (Sum.inl (Sum.inl ()))).nth (n : ℤ) = default)
    (hanchor : (Y (Sum.inl (Sum.inl ()))).nth (-1) = default)
    (hV : V ∈ ktapeSem copyStrWrev CopyState.copy Y) :
    ∀ x, V (Sum.inl x) = Y (Sum.inl x) := by
  rw [copyStrWrev, ktapeSem_renameBank, Part.mem_map_iff] at hV
  obtain ⟨UL, hUL, rfl⟩ := hV
  obtain ⟨hfrozen, hleft⟩ := ktapeSem_liftL_mem copyStrRev CopyState.copy hUL
  intro x; cases x with
  | inl u =>
    cases u
    show UL (bankEquiv.symm (Sum.inl (Sum.inl ()))) = Y (Sum.inl (Sum.inl ()))
    exact copyStrRev_preserves_src (fun i => Y (bankEquiv (Sum.inl i))) (UL ∘ Sum.inl) n
      hblock hend hanchor hleft
  | inr c =>
    show UL (bankEquiv.symm (Sum.inl (Sum.inr c))) = Y (Sum.inl (Sum.inr c))
    exact congrFun hfrozen c

/-- **The wrapper reverse copy halts on block data** (target unconstrained).  Built by
transporting `copyStrRev_output_mem` through `liftL` + `renameBank bankEquiv`. -/
theorem copyStrWrev_output_exists (Y : (Unit ⊕ Fin 1) ⊕ Unit → Tape Γ) (n : ℕ)
    (hblock : ∀ i : ℕ, i < n → (Y (Sum.inl (Sum.inl ()))).nth i ≠ default)
    (hend : (Y (Sum.inl (Sum.inl ()))).nth (n : ℤ) = default)
    (hanchor : (Y (Sum.inl (Sum.inl ()))).nth (-1) = default) :
    ∃ W, W ∈ ktapeSem copyStrWrev CopyState.copy Y := by
  rw [copyStrWrev, ktapeSem_renameBank,
    show (fun i => Y (bankEquiv i))
        = withR ((fun i => Y (bankEquiv i)) ∘ Sum.inr) (fun i => Y (bankEquiv (Sum.inl i))) from
        (Sum.elim_comp_inl_inr (fun i => Y (bankEquiv i))).symm,
    ktapeSem_liftL]
  exact ⟨_, (Part.mem_map_iff _).mpr ⟨_, (Part.mem_map_iff _).mpr
    ⟨_, copyStrRev_output_mem n (fun i => Y (bankEquiv (Sum.inl i))) hblock hend hanchor, rfl⟩, rfl⟩⟩

/-- **The reverse leg `B'` blanks the (block) ancilla and restores the work.**
Full-string analogue of `bennettB'_blanks`: `B'` runs `phaseF2 ; copyStrWrev ;
phaseU2`.  On a work block `liftWork U` (with `M₀` mapping `U` to the block `T`) and
an ancilla `S` blank outside the answer's extent `[0,n)`, it computes the descriptor
of `M₀ U`, blanks the block ancilla, and uncomputes the work back to `liftWork U`.
The output is `liftWork U` with a blank ancilla, independent of `S`'s content. -/
theorem bennettBStr'_blanks (M₀ : KMachine Γ Λ Unit) (q₀ : Λ) (U T : Unit → Tape Γ) (n : ℕ)
    (hUT : T ∈ ktapeSem M₀ q₀ U)
    (hTblock : ∀ i : ℕ, i < n → (T ()).nth i ≠ default)
    (hTend : (T ()).nth (n : ℤ) = default)
    (hTanchor : (T ()).nth (-1) = default)
    (S : Unit → Tape (BennettAlph2 Γ Λ Unit))
    (hSout : ∀ m : ℤ, ¬(0 ≤ m ∧ m < (n : ℤ)) → (S ()).nth m = default) :
    withR (fun _ : Unit => (default : Tape (BennettAlph2 Γ Λ Unit))) (liftWork M₀ U)
      ∈ ktapeSem (bennettBStr' M₀) (Sum.inl (BennettState2.A1 q₀))
          (withR S (liftWork M₀ U)) := by
  classical
  obtain ⟨Y, hY, hYwork⟩ := phaseF2_forward_correct M₀ q₀ U T hUT
  set Uf : (Unit ⊕ Fin 1) ⊕ Unit → Tape (BennettAlph2 Γ Λ Unit) := withR S Y with hUf
  have hUfmem : Uf ∈ ktapeSem (liftL (phaseF2 M₀) (κ := Unit)) (BennettState2.A1 q₀)
      (withR S (liftWork M₀ U)) := by
    rw [ktapeSem_liftL, Part.mem_map_iff]; exact ⟨Y, hY, rfl⟩
  -- the work after F' is `map inlMap (T ())`; describe its `nth` cellwise
  have hUfwork_nth : ∀ m : ℤ,
      (Uf (Sum.inl (Sum.inl ()))).nth m = Sum.inl ((T ()).nth m) := by
    intro m; show (Y (Sum.inl ())).nth m = Sum.inl ((T ()).nth m)
    rw [hYwork (), Tape.map_nth]; rfl
  have hwork_block : ∀ i : ℕ, i < n → (Uf (Sum.inl (Sum.inl ()))).nth (i : ℤ) ≠ default := by
    intro i hi; rw [hUfwork_nth]; intro hc
    have h2 : (Sum.inl ((T ()).nth (i : ℤ)) : BennettAlph2 Γ Λ Unit) = Sum.inl default := hc
    exact hTblock i hi (Sum.inl.inj h2)
  have hwork_end : (Uf (Sum.inl (Sum.inl ()))).nth (n : ℤ) = default := by
    rw [hUfwork_nth]; exact congrArg Sum.inl hTend
  have hwork_anchor : (Uf (Sum.inl (Sum.inl ()))).nth (-1) = default := by
    rw [hUfwork_nth]; exact congrArg Sum.inl hTanchor
  have hanc_out : ∀ m : ℤ, ¬(0 ≤ m ∧ m < (n : ℤ)) → (Uf (Sum.inr ())).nth m = default := by
    intro m hm; show (S ()).nth m = default; exact hSout m hm
  obtain ⟨W, hWmem⟩ :=
    copyStrWrev_output_exists Uf n hwork_block hwork_end hwork_anchor
  have hWinlY : W ∘ Sum.inl = Y := by
    funext x; show W (Sum.inl x) = Y x
    rw [copyStrWrev_preserves_left Uf W n hwork_block hwork_end hwork_anchor hWmem x]; rfl
  have hWinr : W (Sum.inr ()) = default :=
    copyStrWrev_blanks Uf W n hwork_block hwork_end hwork_anchor hanc_out hWmem
  have hUuncompute : liftWork M₀ U ∈
      ktapeSem (phaseU2 M₀) UncompState.RStart (W ∘ Sum.inl) := by
    rw [hWinlY]
    exact (phaseF2_semInverse M₀ q₀).fwd (liftWork M₀ U) Y (liftWork_WFblank M₀ U) hY
  have hanc : (fun _ : Unit => (default : Tape (BennettAlph2 Γ Λ Unit))) = W ∘ Sum.inr := by
    funext j; cases j; exact hWinr.symm
  rw [bennettBStr', ktapeSem_seq, Part.mem_bind_iff]
  refine ⟨Uf, hUfmem, ?_⟩
  rw [ktapeSem_seq, Part.mem_bind_iff]
  refine ⟨W, hWmem, ?_⟩
  rw [show W = withR (W ∘ Sum.inr) (W ∘ Sum.inl) from (Sum.elim_comp_inl_inr W).symm,
      ktapeSem_liftL, Part.mem_map_iff]
  refine ⟨liftWork M₀ U, hUuncompute, ?_⟩
  rw [← hanc]

/-! ### The full-string Bennett involution `D = B ; swap ; B'` (conj-4) -/

/-- The full-string Bennett involution machine `D = bennettBStr ; swap ; bennettBStr'`. -/
noncomputable def bennettBStrD (M₀ : KMachine Γ Λ Unit) (q₀ : Λ) :=
  seq (seq (bennettBStr M₀) (bankSwap (wAncSwap (ι := Unit))) false) (bennettBStr' M₀)
      (Sum.inl (BennettState2.A1 q₀))

/-- **`D` simulates `M₀` on block involutive points.**  Full-string analogue of
`bennettD_simulates`: for block `A`, `U` with `M₀ A = U` and `M₀ U = A` (the
involution), `D` maps `enc A = (liftWork A, blank ancilla)` to `enc U`.  Chains
`bennettBStr_correct_full` (B) → work↔ancilla swap → `bennettBStr'_blanks` (B'), the
latter on the block ancilla `liftWork A` (blank outside the answer's extent). -/
theorem bennettBStrD_simulates (M₀ : KMachine Γ Λ Unit) (q₀ : Λ) (A U : Unit → Tape Γ)
    (hA : ∀ j, IsBlock (A j)) (hU : ∀ j, IsBlock (U j))
    (hAU : U ∈ ktapeSem M₀ q₀ A) (hUA : A ∈ ktapeSem M₀ q₀ U) :
    withR (fun _ : Unit => (default : Tape (BennettAlph2 Γ Λ Unit))) (liftWork M₀ U)
      ∈ ktapeSem (bennettBStrD M₀ q₀)
          (Sum.inl (Sum.inl (Sum.inl (Sum.inl (BennettState2.A1 q₀)))))
          (withR (fun _ : Unit => (default : Tape (BennettAlph2 Γ Λ Unit))) (liftWork M₀ A)) := by
  classical
  have hB := bennettBStr_correct_full M₀ q₀ A U hU hAU
  set ZB : (Unit ⊕ Fin 1) ⊕ Unit → Tape (BennettAlph2 Γ Λ Unit) :=
    withR (fun j => liftWork M₀ U (Sum.inl j)) (liftWork M₀ A) with hZB
  set VB : (Unit ⊕ Fin 1) ⊕ Unit → Tape (BennettAlph2 Γ Λ Unit) :=
    withR (fun j => liftWork M₀ A (Sum.inl j)) (liftWork M₀ U) with hVB
  -- swap leg: VB = swap(ZB)
  have hswap : VB ∈ ktapeSem (bankSwap (wAncSwap (ι := Unit))) false ZB := by
    have hstep : kstep (bankSwap (wAncSwap (ι := Unit)) (Γ := BennettAlph2 Γ Λ Unit))
        ⟨false, ZB⟩ = some ⟨true, (KStmt.perm (wAncSwap (ι := Unit))).apply ZB⟩ := by
      simp [kstep, bankSwap]
    have hhalt : kstep (bankSwap (wAncSwap (ι := Unit)) (Γ := BennettAlph2 Γ Λ Unit))
        (⟨true, (KStmt.perm (wAncSwap (ι := Unit))).apply ZB⟩ :
          KCfg (BennettAlph2 Γ Λ Unit) Bool ((Unit ⊕ Fin 1) ⊕ Unit)) = none := by
      simp [kstep, bankSwap]
    have hVBeq : VB = (KStmt.perm (wAncSwap (ι := Unit))).apply ZB := by
      funext i
      show VB i = ZB ((wAncSwap (ι := Unit))⁻¹ i)
      rw [wAncSwap_selfInverse]
      rcases i with (j | h) | j <;> rfl
    rw [hVBeq]
    exact (Part.mem_map_iff _).mpr
      ⟨⟨true, (KStmt.perm (wAncSwap (ι := Unit))).apply ZB⟩,
        StateTransition.mem_eval.mpr
          ⟨Relation.ReflTransGen.single (Option.mem_def.mpr hstep), hhalt⟩, rfl⟩
  -- B' leg: blanks the (block) ancilla S = liftWork A, restores work to liftWork U
  obtain ⟨n, hAblock, hAout⟩ := hA ()
  have hBp := bennettBStr'_blanks M₀ q₀ U A n hUA hAblock
    (hAout (n : ℤ) (by omega)) (hAout (-1) (by omega))
    (fun j => liftWork M₀ A (Sum.inl j))
    (fun m hm => by
      show (Tape.map inlMap (A ())).nth m = default
      rw [Tape.map_nth]; exact congrArg Sum.inl (hAout m hm))
  -- assemble D = B ; swap ; B'
  rw [bennettBStrD, ktapeSem_seq, Part.mem_bind_iff]
  refine ⟨VB, ?_, hBp⟩
  rw [ktapeSem_seq, Part.mem_bind_iff]
  exact ⟨ZB, hB, hswap⟩

/-- **Block-data unconditional symmetrisation (the general statement).**  Let `M₀`
compute a partial involution (`hInvol`) and preserve blockness (`hblk`: a block input
has a block output).  Then there is a machine `D` over the Bennett alphabet — with no
`KReversible` hypothesis on `M₀` — and an encoding `enc` such that on every block
input `A` with `M₀ A = U`, `D` simulates `M₀` (`enc U ∈ ⟦D⟧ (enc A)`) and is
involutive on the encoded points (`enc A ∈ ⟦D⟧ (enc U)`).  The full-string analogue
of `nakano_symmetrisation_headvalued`, lifting it from single-cell to block data. -/
theorem nakano_symmetrisation_strvalued (M₀ : KMachine Γ Λ Unit) (q₀ : Λ)
    (hInvol : ∀ X Y, Y ∈ ktapeSem M₀ q₀ X → X ∈ ktapeSem M₀ q₀ Y)
    (hblk : ∀ X Y, (∀ j, IsBlock (X j)) → Y ∈ ktapeSem M₀ q₀ X → ∀ j, IsBlock (Y j)) :
    ∃ (q0' : _)
      (enc : (Unit → Tape Γ) → ((Unit ⊕ Fin 1) ⊕ Unit → Tape (BennettAlph2 Γ Λ Unit))),
      ∀ A U, (∀ j, IsBlock (A j)) → U ∈ ktapeSem M₀ q₀ A →
        enc U ∈ ktapeSem (bennettBStrD M₀ q₀) q0' (enc A) ∧
        enc A ∈ ktapeSem (bennettBStrD M₀ q₀) q0' (enc U) := by
  refine ⟨Sum.inl (Sum.inl (Sum.inl (Sum.inl (BennettState2.A1 q₀)))),
    (fun A => withR (fun _ : Unit => (default : Tape (BennettAlph2 Γ Λ Unit)))
      (liftWork M₀ A)), ?_⟩
  intro A U hA hAU
  have hU : ∀ j, IsBlock (U j) := hblk A U hA hAU
  have hUA : A ∈ ktapeSem M₀ q₀ U := hInvol A U hAU
  exact ⟨bennettBStrD_simulates M₀ q₀ A U hA hU hAU hUA,
         bennettBStrD_simulates M₀ q₀ U A hU hA hUA hAU⟩

/-! ### Multi-tape conjugation: per-pair ancilla fill (conj-5a)

The multi-tape conjugation copies all `k` tapes via `copyMultiK = copyPairs`.  Its
ancilla-fill primitive is `copyStrAt_anc_full`: a designated-pair copy `s → t` on a
block source writes the whole source block onto the target `t`.  Transports
`copyStr_tgt_eq_src` through `liftL` + `renameBank (selEquiv s t)`. -/

/-- `(selEquiv s t).symm` sends the target bank `t` to the copy's target slot
`Sum.inl (Sum.inr ())`.  Mirror of `selEquiv_symm_s`. -/
theorem selEquiv_symm_t {ι' : Type*} [DecidableEq ι'] (s t : ι') (hst : s ≠ t) :
    (selEquiv s t hst).symm t = Sum.inl (Sum.inr ()) := by
  have hpt : activeP s t t := Or.inr rfl
  simp only [selEquiv, Equiv.symm_trans_apply, Equiv.sumCompl_symm_apply_of_pos hpt,
    Equiv.sumCongr_symm, Equiv.refl_symm, Equiv.sumCongr_apply, Sum.map_inl]
  congr 1
  show (if t = s then Sum.inl () else Sum.inr ()) = Sum.inr ()
  rw [if_neg (Ne.symm hst)]

/-- **The designated-pair copy fills the target with the source block.**  On a block
source `s` and a blank target `t`, `copyStrAt s t` writes the whole source block onto
`t` (`V t = Y s`).  Per-tape primitive of the multi-tape ancilla fill; the
`selEquiv`-transported analogue of `copyStrW_anc_full`. -/
theorem copyStrAt_anc_full {ι' : Type*} [DecidableEq ι'] (s t : ι') (hst : s ≠ t)
    (Y V : ι' → Tape Γ) (hblk : IsBlock (Y s)) (htgt : ∀ m : ℤ, (Y t).nth m = default)
    (hV : V ∈ ktapeSem (copyStrAt s t hst) CopyState.copy Y) :
    V t = Y s := by
  rw [copyStrAt, ktapeSem_renameBank, Part.mem_map_iff] at hV
  obtain ⟨UL, hUL, rfl⟩ := hV
  obtain ⟨hfroz, hleft⟩ := ktapeSem_liftL_mem copyStr CopyState.copy hUL
  show UL ((selEquiv s t hst).symm t) = Y s
  rw [selEquiv_symm_t]
  have key := copyStr_tgt_eq_src (fun i => Y (selEquiv s t hst (Sum.inl i))) (UL ∘ Sum.inl)
    (by show IsBlock (Y (selEquiv s t hst (Sum.inl (Sum.inl ()))))
        rw [selEquiv_inl_inl]; exact hblk)
    (by intro m; show (Y (selEquiv s t hst (Sum.inl (Sum.inr ())))).nth m = default
        rw [selEquiv_inl_inr]; exact htgt m)
    hleft
  simp only [selEquiv_inl_inl] at key
  exact key

/-- **The copy fold fills every target with its source block.**  On a domain where
each pair's source is a block (`hblk`) and the targets are pairwise independent
(`PairsDomIn`), the fold `copyPairs l` writes each pair's source block onto its
target: `V p.1.2 = X p.1.1`.  Head leg via `copyStrAt_anc_full`; the target then
survives the tail (`copyPairs_preserves`, target untouched by later pairs); tail
pairs by induction (the head preserves their source). -/
theorem copyPairs_targets {ι' : Type*} [DecidableEq ι'] :
    (l : List {p : ι' × ι' // p.1 ≠ p.2}) → (X V : ι' → Tape Γ) →
    PairsDomIn l X → (∀ p ∈ l, IsBlock (X p.1.1)) →
    V ∈ ktapeSem (copyPairs l) (foldStart l) X →
    ∀ p ∈ l, V p.1.2 = X p.1.1
  | [], X, V, _, _, _ => by intro p hp; simp at hp
  | p₀ :: rest, X, V, hX, hblk, hV => by
    have hbind : V ∈ (ktapeSem (copyStrAt p₀.1.1 p₀.1.2 p₀.2) CopyState.copy X).bind
        (ktapeSem (copyPairs rest) (foldStart rest)) := by
      rw [← ktapeSem_seq]; exact hV
    rw [Part.mem_bind_iff] at hbind
    obtain ⟨W, hW, hVrest⟩ := hbind
    have hWanc : W p₀.1.2 = X p₀.1.1 :=
      copyStrAt_anc_full p₀.1.1 p₀.1.2 p₀.2 X W (hblk p₀ (by simp)) hX.1.2.1 hW
    have hpres := copyStrAt_preserves_others p₀.1.1 p₀.1.2 p₀.2 X W
      ((copyDomAt_iff p₀.1.1 p₀.1.2 p₀.2 X).mpr hX.1) hW
    have hWdom : PairsDomIn rest W := by
      refine (PairsDomIn_congr rest ?_).mpr hX.2.1
      intro q hq
      have hind := hX.2.2 q hq
      exact ⟨hpres q.1.1 (Ne.symm hind.1), hpres q.1.2 (Ne.symm hind.2)⟩
    have hWblk : ∀ q ∈ rest, IsBlock (W q.1.1) := by
      intro q hq
      have hind := hX.2.2 q hq
      rw [hpres q.1.1 (Ne.symm hind.1)]
      exact hblk q (by simp [hq])
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hprest
    · have hVp : V p.1.2 = W p.1.2 :=
        copyPairs_preserves rest W V hWdom hVrest p.1.2 (fun q hq => (hX.2.2 q hq).2)
      rw [hVp, hWanc]
    · have hIH := copyPairs_targets rest W V hWdom hWblk hVrest p hprest
      have hind := hX.2.2 p hprest
      rw [hIH, hpres p.1.1 (Ne.symm hind.1)]

/-- **The multi-tape copy fills each ancilla with its work block.**  On the clean
per-tape domain with each work tape a block, `copyMultiK k` copies every work tape
`Sum.inl (Sum.inl j)` onto its ancilla `Sum.inr j` in full: `V (Sum.inr j) =
X (Sum.inl (Sum.inl j))`.  The forward copy-content counterpart of
`copyMultiK_preserves_left`. -/
theorem copyMultiK_anc_full (k : ℕ) (X V : ((Fin k ⊕ Fin 1) ⊕ Fin k) → Tape Γ)
    (hX : MultiDomIn k X) (hblk : ∀ j, IsBlock (X (Sum.inl (Sum.inl j))))
    (hV : V ∈ ktapeSem (copyMultiK k) (foldStart (tapePairs k)) X) :
    ∀ j, V (Sum.inr j) = X (Sum.inl (Sum.inl j)) := by
  intro j
  have hpblk : ∀ p ∈ tapePairs k, IsBlock (X p.1.1) := by
    intro p hp
    rw [tapePairs, List.mem_ofFn] at hp
    obtain ⟨i, rfl⟩ := hp
    exact hblk i
  have hmem : tapePair k j ∈ tapePairs k := by
    rw [tapePairs, List.mem_ofFn]; exact ⟨j, rfl⟩
  exact copyPairs_targets (tapePairs k) X V (pairsDomIn_tapePairs k X hX) hpblk hV
    (tapePair k j) hmem

/-! ### Multi-tape conjugation: per-pair reverse primitives (conj-5c) -/

/-- **The designated-pair reverse copy blanks the target.**  On a block source `s`
(length `n`) and a target `t` blank outside `[0,n)`, `copyStrAtRev s t` blanks `t`
entirely (`V t = default`).  `selEquiv`-transported analogue of
`copyStrWrev_blanks`. -/
theorem copyStrAtRev_blanks {ι' : Type*} [DecidableEq ι'] (s t : ι') (hst : s ≠ t)
    (Y V : ι' → Tape Γ) (n : ℕ)
    (hblock : ∀ i : ℕ, i < n → (Y s).nth i ≠ default)
    (hend : (Y s).nth (n : ℤ) = default)
    (hanchor : (Y s).nth (-1) = default)
    (htgtout : ∀ m : ℤ, ¬(0 ≤ m ∧ m < (n : ℤ)) → (Y t).nth m = default)
    (hV : V ∈ ktapeSem (copyStrAtRev s t hst) CopyState.copy Y) :
    V t = default := by
  rw [copyStrAtRev, ktapeSem_renameBank, Part.mem_map_iff] at hV
  obtain ⟨UL, hUL, rfl⟩ := hV
  obtain ⟨hfroz, hleft⟩ := ktapeSem_liftL_mem copyStrRev CopyState.copy hUL
  show UL ((selEquiv s t hst).symm t) = default
  rw [selEquiv_symm_t]
  exact copyStrRev_tgt_blank (fun i => Y (selEquiv s t hst (Sum.inl i))) (UL ∘ Sum.inl) n
    (by intro i hi
        show (Y (selEquiv s t hst (Sum.inl (Sum.inl ())))).nth (i : ℤ) ≠ default
        rw [selEquiv_inl_inl]; exact hblock i hi)
    (by show (Y (selEquiv s t hst (Sum.inl (Sum.inl ())))).nth (n : ℤ) = default
        rw [selEquiv_inl_inl]; exact hend)
    (by show (Y (selEquiv s t hst (Sum.inl (Sum.inl ())))).nth (-1) = default
        rw [selEquiv_inl_inl]; exact hanchor)
    (by intro m hm
        show (Y (selEquiv s t hst (Sum.inl (Sum.inr ())))).nth m = default
        rw [selEquiv_inl_inr]; exact htgtout m hm)
    hleft

/-- **The designated-pair reverse copy changes only the target bank `t`.**  Source
`s` preserved (`copyStrRev_preserves_src`, on the block facts) and every frozen bank
preserved (`liftL`).  Reverse analogue of `copyStrAt_preserves_others`. -/
theorem copyStrAtRev_preserves_others {ι' : Type*} [DecidableEq ι'] (s t : ι') (hst : s ≠ t)
    (Y V : ι' → Tape Γ) (n : ℕ)
    (hblock : ∀ i : ℕ, i < n → (Y s).nth i ≠ default)
    (hend : (Y s).nth (n : ℤ) = default)
    (hanchor : (Y s).nth (-1) = default)
    (hV : V ∈ ktapeSem (copyStrAtRev s t hst) CopyState.copy Y) :
    ∀ b, b ≠ t → V b = Y b := by
  rw [copyStrAtRev, ktapeSem_renameBank, Part.mem_map_iff] at hV
  obtain ⟨UL, hUL, rfl⟩ := hV
  obtain ⟨hfroz, hleft⟩ := ktapeSem_liftL_mem copyStrRev CopyState.copy hUL
  intro b hbt
  show UL ((selEquiv s t hst).symm b) = Y b
  by_cases hbs : b = s
  · rw [hbs]
    rw [selEquiv_symm_s]
    have hp := copyStrRev_preserves_src (fun i => Y (selEquiv s t hst (Sum.inl i)))
      (UL ∘ Sum.inl) n
      (by intro i hi
          show (Y (selEquiv s t hst (Sum.inl (Sum.inl ())))).nth (i : ℤ) ≠ default
          rw [selEquiv_inl_inl]; exact hblock i hi)
      (by show (Y (selEquiv s t hst (Sum.inl (Sum.inl ())))).nth (n : ℤ) = default
          rw [selEquiv_inl_inl]; exact hend)
      (by show (Y (selEquiv s t hst (Sum.inl (Sum.inl ())))).nth (-1) = default
          rw [selEquiv_inl_inl]; exact hanchor)
      hleft
    simp only [Function.comp_apply, selEquiv_inl_inl] at hp
    exact hp
  · have hnotactive : ¬ activeP s t b := by
      show ¬ (b = s ∨ b = t); rintro (h | h)
      exacts [hbs h, hbt h]
    rw [selEquiv_symm_frozen s t hst b hnotactive]
    have hf := congrFun hfroz ⟨b, hnotactive⟩
    simp only [Function.comp_apply, selEquiv_inr] at hf
    exact hf

/-! ### Multi-tape conjugation: reverse fold blanks the ancillas (conj-5c) -/

/-- **The reverse copy fold preserves every bank it does not target.**  Reverse
analogue of `copyPairs_preserves`: with each source a block (for the per-pair
source-preservation) and each pair's source/target disjoint from later targets
(`hpw`), `copyPairsRev l` fixes any bank that is no pair's target. -/
theorem copyPairsRev_preserves {ι' : Type*} [DecidableEq ι'] :
    (l : List {p : ι' × ι' // p.1 ≠ p.2}) → (X V : ι' → Tape Γ) →
    (∀ p ∈ l, IsBlock (X p.1.1)) →
    l.Pairwise (fun p q => p.1.1 ≠ q.1.2 ∧ p.1.2 ≠ q.1.2) →
    V ∈ ktapeSem (copyPairsRev l) (foldStartRev l) X →
    ∀ b, (∀ p ∈ l, b ≠ p.1.2) → V b = X b
  | [], X, V, _, _, hV => by
      intro b _
      have hVh : V ∈ ktapeSem (haltMachine (Γ := Γ) (ι' := ι')) () X := hV
      rw [ktapeSem_haltMachine, Part.mem_some_iff] at hVh
      rw [hVh]
  | p₀ :: rest, X, V, hsrc, hpw, hV => by
      intro b hb
      have hbind : V ∈ (ktapeSem (copyPairsRev rest) (foldStartRev rest) X).bind
          (ktapeSem (copyStrAtRev p₀.1.1 p₀.1.2 p₀.2) CopyState.copy) := by
        rw [← ktapeSem_seq]; exact hV
      rw [Part.mem_bind_iff] at hbind
      obtain ⟨W, hW, hVc⟩ := hbind
      obtain ⟨hpwhead, hpwrest⟩ := List.pairwise_cons.mp hpw
      have hWpres : ∀ c, (∀ q ∈ rest, c ≠ q.1.2) → W c = X c :=
        copyPairsRev_preserves rest X W (fun q hq => hsrc q (by simp [hq])) hpwrest hW
      have hWsrc : W p₀.1.1 = X p₀.1.1 := hWpres p₀.1.1 (fun q hq => (hpwhead q hq).1)
      obtain ⟨n, hbk, hout⟩ := hsrc p₀ (by simp)
      have hVb : V b = W b :=
        copyStrAtRev_preserves_others p₀.1.1 p₀.1.2 p₀.2 W V n
          (by intro i hi; rw [hWsrc]; exact hbk i hi)
          (by rw [hWsrc]; exact hout (n : ℤ) (by omega))
          (by rw [hWsrc]; exact hout (-1) (by omega))
          hVc b (hb p₀ (by simp))
      rw [hVb, hWpres b (fun q hq => hb q (by simp [hq]))]

/-- **The reverse copy fold blanks every target.**  When each source is a block and
each target *equals its source* (the configuration B' meets after the swap: both work
and ancilla hold the same lifted block), `copyPairsRev l` blanks every target:
`V p.1.2 = default`.  Outer pair blanked by its `copyStrAtRev` (`copyStrAtRev_blanks`,
target=source so blank-outside holds); tail targets blanked by induction and survive
the outer copy (`copyStrAtRev_preserves_others`). -/
theorem copyPairsRev_blanks {ι' : Type*} [DecidableEq ι'] :
    (l : List {p : ι' × ι' // p.1 ≠ p.2}) → (X V : ι' → Tape Γ) →
    (∀ p ∈ l, IsBlock (X p.1.1)) → (∀ p ∈ l, X p.1.2 = X p.1.1) →
    l.Pairwise (fun p q => p.1.1 ≠ q.1.2 ∧ p.1.2 ≠ q.1.2) →
    V ∈ ktapeSem (copyPairsRev l) (foldStartRev l) X →
    ∀ p ∈ l, V p.1.2 = default
  | [], _, _, _, _, _, _ => by intro p hp; simp at hp
  | p₀ :: rest, X, V, hsrc, htgt, hpw, hV => by
      have hbind : V ∈ (ktapeSem (copyPairsRev rest) (foldStartRev rest) X).bind
          (ktapeSem (copyStrAtRev p₀.1.1 p₀.1.2 p₀.2) CopyState.copy) := by
        rw [← ktapeSem_seq]; exact hV
      rw [Part.mem_bind_iff] at hbind
      obtain ⟨W, hW, hVc⟩ := hbind
      obtain ⟨hpwhead, hpwrest⟩ := List.pairwise_cons.mp hpw
      have hWpres : ∀ c, (∀ q ∈ rest, c ≠ q.1.2) → W c = X c :=
        copyPairsRev_preserves rest X W (fun q hq => hsrc q (by simp [hq])) hpwrest hW
      obtain ⟨n, hbk, hout⟩ := hsrc p₀ (by simp)
      have hWsrc : W p₀.1.1 = X p₀.1.1 := hWpres p₀.1.1 (fun q hq => (hpwhead q hq).1)
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hprest
      · have hWtgt : W p.1.2 = X p.1.1 := by
          rw [hWpres p.1.2 (fun q hq => (hpwhead q hq).2)]; exact htgt p (by simp)
        exact copyStrAtRev_blanks p.1.1 p.1.2 p.2 W V n
          (by intro i hi; rw [hWsrc]; exact hbk i hi)
          (by rw [hWsrc]; exact hout (n : ℤ) (by omega))
          (by rw [hWsrc]; exact hout (-1) (by omega))
          (by intro m hm; rw [hWtgt]; exact hout m hm)
          hVc
      · have hWblank : W p.1.2 = default :=
          copyPairsRev_blanks rest X W (fun q hq => hsrc q (by simp [hq]))
            (fun q hq => htgt q (by simp [hq])) hpwrest hW p hprest
        have hVeq : V p.1.2 = W p.1.2 :=
          copyStrAtRev_preserves_others p₀.1.1 p₀.1.2 p₀.2 W V n
            (by intro i hi; rw [hWsrc]; exact hbk i hi)
            (by rw [hWsrc]; exact hout (n : ℤ) (by omega))
            (by rw [hWsrc]; exact hout (-1) (by omega))
            hVc p.1.2 (Ne.symm (hpwhead p hprest).2)
        rw [hVeq, hWblank]

/-- **The multi-tape reverse copy blanks every ancilla.**  When each work tape is a
block and each ancilla equals its work tape, `copyMultiKRev k` blanks all ancillas:
`V (Sum.inr j) = default`.  The reverse counterpart of `copyMultiK_anc_full`. -/
theorem copyMultiKRev_blanks (k : ℕ) (X V : ((Fin k ⊕ Fin 1) ⊕ Fin k) → Tape Γ)
    (hsrc : ∀ j, IsBlock (X (Sum.inl (Sum.inl j))))
    (htgt : ∀ j, X (Sum.inr j) = X (Sum.inl (Sum.inl j)))
    (hV : V ∈ ktapeSem (copyMultiKRev k) (foldStartRev (tapePairs k)) X) :
    ∀ j, V (Sum.inr j) = default := by
  intro j
  have hpsrc : ∀ p ∈ tapePairs k, IsBlock (X p.1.1) := by
    intro p hp; rw [tapePairs, List.mem_ofFn] at hp; obtain ⟨i, rfl⟩ := hp; exact hsrc i
  have hptgt : ∀ p ∈ tapePairs k, X p.1.2 = X p.1.1 := by
    intro p hp; rw [tapePairs, List.mem_ofFn] at hp; obtain ⟨i, rfl⟩ := hp; exact htgt i
  have hpw : (tapePairs k).Pairwise (fun p q => p.1.1 ≠ q.1.2 ∧ p.1.2 ≠ q.1.2) := by
    rw [tapePairs, List.pairwise_ofFn]
    intro a b hab
    refine ⟨by simp [tapePair], ?_⟩
    simp only [tapePair, ne_eq, Sum.inr.injEq]
    exact Fin.ne_of_lt hab
  have hmem : tapePair k j ∈ tapePairs k := by
    rw [tapePairs, List.mem_ofFn]; exact ⟨j, rfl⟩
  exact copyPairsRev_blanks (tapePairs k) X V hpsrc hptgt hpw hV (tapePair k j) hmem

/-! ### Multi-tape wrapper correctness on block data (conj-5d) -/

/-- A block source with a blank target meets `CopyDomAt`. -/
theorem copyDomAt_of_isBlock {ι' : Type*} (s t : ι') (X : ι' → Tape Γ)
    (hblk : IsBlock (X s)) (htgt : ∀ m : ℤ, (X t).nth m = default) : CopyDomAt s t X := by
  obtain ⟨n, hbk, hout⟩ := hblk
  exact ⟨hout (-1) (by omega), htgt, n, hbk, hout (n : ℤ) (by omega)⟩

/-- **The designated-pair copy halts on a block source.**  Transports
`copyStr_output_mem` through `liftL` + `renameBank (selEquiv s t)`. -/
theorem copyStrAt_output_exists {ι' : Type*} [DecidableEq ι'] (s t : ι') (hst : s ≠ t)
    (Y : ι' → Tape Γ) (hblk : IsBlock (Y s)) :
    ∃ W, W ∈ ktapeSem (copyStrAt s t hst) CopyState.copy Y := by
  obtain ⟨n, hblock, hout⟩ := hblk
  rw [copyStrAt, ktapeSem_renameBank,
    show (fun i => Y (selEquiv s t hst i))
        = withR ((fun i => Y (selEquiv s t hst i)) ∘ Sum.inr)
            (fun i => Y (selEquiv s t hst (Sum.inl i))) from
        (Sum.elim_comp_inl_inr (fun i => Y (selEquiv s t hst i))).symm,
    ktapeSem_liftL]
  exact ⟨_, (Part.mem_map_iff _).mpr ⟨_, (Part.mem_map_iff _).mpr
    ⟨_, copyStr_output_mem n (fun i => Y (selEquiv s t hst (Sum.inl i)))
        (by intro i hi
            show (Y (selEquiv s t hst (Sum.inl (Sum.inl ())))).nth i ≠ default
            rw [selEquiv_inl_inl]; exact hblock i hi)
        (by show (Y (selEquiv s t hst (Sum.inl (Sum.inl ())))).nth (n : ℤ) = default
            rw [selEquiv_inl_inl]; exact hout (n : ℤ) (by omega))
        (by show (Y (selEquiv s t hst (Sum.inl (Sum.inl ())))).nth (-1) = default
            rw [selEquiv_inl_inl]; exact hout (-1) (by omega)),
      rfl⟩, rfl⟩⟩

/-- **The copy fold halts on block sources.**  Each pair's copy halts
(`copyStrAt_output_exists`) and the fold composes; the tail's domain transfers
through the head copy (`copyStrAt_preserves_others`). -/
theorem copyPairs_output_exists {ι' : Type*} [DecidableEq ι'] :
    (l : List {p : ι' × ι' // p.1 ≠ p.2}) → (X : ι' → Tape Γ) →
    PairsDomIn l X → (∀ p ∈ l, IsBlock (X p.1.1)) →
    ∃ V, V ∈ ktapeSem (copyPairs l) (foldStart l) X
  | [], X, _, _ => ⟨X, by
      show X ∈ ktapeSem (haltMachine (Γ := Γ) (ι' := ι')) () X
      rw [ktapeSem_haltMachine]; exact Part.mem_some X⟩
  | p :: rest, X, hX, hblk => by
      obtain ⟨W, hW⟩ := copyStrAt_output_exists p.1.1 p.1.2 p.2 X (hblk p (by simp))
      have hpres := copyStrAt_preserves_others p.1.1 p.1.2 p.2 X W
        ((copyDomAt_iff p.1.1 p.1.2 p.2 X).mpr hX.1) hW
      have hWdom : PairsDomIn rest W :=
        (PairsDomIn_congr rest (fun q hq =>
          ⟨hpres q.1.1 (Ne.symm (hX.2.2 q hq).1), hpres q.1.2 (Ne.symm (hX.2.2 q hq).2)⟩)).mpr hX.2.1
      have hWblk : ∀ q ∈ rest, IsBlock (W q.1.1) := fun q hq => by
        rw [hpres q.1.1 (Ne.symm (hX.2.2 q hq).1)]; exact hblk q (by simp [hq])
      obtain ⟨V, hV⟩ := copyPairs_output_exists rest W hWdom hWblk
      refine ⟨V, ?_⟩
      have hVm : V ∈ (ktapeSem (copyStrAt p.1.1 p.1.2 p.2) CopyState.copy X).bind
          (ktapeSem (copyPairs rest) (foldStart rest)) := Part.mem_bind_iff.mpr ⟨W, hW, hV⟩
      rw [← ktapeSem_seq] at hVm
      exact hVm

/-- **The multi-tape copy halts on block data.** -/
theorem copyMultiK_output_exists (k : ℕ) (X : ((Fin k ⊕ Fin 1) ⊕ Fin k) → Tape Γ)
    (hX : MultiDomIn k X) (hblk : ∀ j, IsBlock (X (Sum.inl (Sum.inl j)))) :
    ∃ W, W ∈ ktapeSem (copyMultiK k) (foldStart (tapePairs k)) X := by
  refine copyPairs_output_exists (tapePairs k) X (pairsDomIn_tapePairs k X hX) ?_
  intro p hp; rw [tapePairs, List.mem_ofFn] at hp; obtain ⟨i, rfl⟩ := hp; exact hblk i

/-- **Exact `bennettBStrK` output on block data.**  Multi-tape analogue of
`bennettBStr_correct_full`: when `M₀` maps `A` to block tapes `U`, the work⊕history
block is restored to `liftWork A` and each ancilla `j` holds `liftWork U` tape `j`
exactly (the whole answer block). -/
theorem bennettBStrK_correct_full (k : ℕ) (M₀ : KMachine Γ Λ (Fin k)) (q₀ : Λ)
    (A U : Fin k → Tape Γ) (hU : ∀ j, IsBlock (U j)) (hAU : U ∈ ktapeSem M₀ q₀ A) :
    withR (fun j => liftWork M₀ U (Sum.inl j)) (liftWork M₀ A)
      ∈ ktapeSem (bennettBStrK k M₀) (Sum.inl (Sum.inl (BennettState2.A1 q₀)))
          (withR (fun _ : Fin k => (default : Tape (BennettAlph2 Γ Λ (Fin k))))
            (liftWork M₀ A)) := by
  classical
  obtain ⟨Y, hY, hYwork⟩ := phaseF2_forward_correct M₀ q₀ A U hAU
  set Uf : (Fin k ⊕ Fin 1) ⊕ Fin k → Tape (BennettAlph2 Γ Λ (Fin k)) :=
    withR (fun _ : Fin k => (default : Tape (BennettAlph2 Γ Λ (Fin k)))) Y with hUf
  have hUfmem : Uf ∈ ktapeSem (liftL (phaseF2 M₀) (κ := Fin k)) (BennettState2.A1 q₀)
      (withR (fun _ : Fin k => (default : Tape (BennettAlph2 Γ Λ (Fin k)))) (liftWork M₀ A)) := by
    rw [ktapeSem_liftL, Part.mem_map_iff]; exact ⟨Y, hY, rfl⟩
  have hblkUf : ∀ j, IsBlock (Uf (Sum.inl (Sum.inl j))) := by
    intro j; show IsBlock (Y (Sum.inl j)); rw [hYwork j]; exact isBlock_map (hU j)
  have hancUf : ∀ j, ∀ m : ℤ, (Uf (Sum.inr j)).nth m = default := by
    intro j m; show ((default : Tape (BennettAlph2 Γ Λ (Fin k)))).nth m = default
    exact Tape.nth_default m
  have hMD : MultiDomIn k Uf := fun j =>
    copyDomAt_of_isBlock (Sum.inl (Sum.inl j)) (Sum.inr j) Uf (hblkUf j) (hancUf j)
  obtain ⟨W, hWmem⟩ := copyMultiK_output_exists k Uf hMD hblkUf
  have hWinlY : W ∘ Sum.inl = Y := by
    funext x; show W (Sum.inl x) = Y x
    rw [copyMultiK_preserves_left k Uf W hMD hWmem x]; rfl
  have hWinrEq : W ∘ Sum.inr = fun j => liftWork M₀ U (Sum.inl j) := by
    funext j; show W (Sum.inr j) = liftWork M₀ U (Sum.inl j)
    rw [copyMultiK_anc_full k Uf W hMD hblkUf hWmem j]
    show Y (Sum.inl j) = liftWork M₀ U (Sum.inl j)
    exact hYwork j
  have hUuncompute : liftWork M₀ A ∈
      ktapeSem (phaseU2 M₀) UncompState.RStart (W ∘ Sum.inl) := by
    rw [hWinlY]
    exact (phaseF2_semInverse M₀ q₀).fwd (liftWork M₀ A) Y (liftWork_WFblank M₀ A) hY
  rw [bennettBStrK, ktapeSem_seq, Part.mem_bind_iff]
  refine ⟨W, ?_, ?_⟩
  · rw [ktapeSem_seq, Part.mem_bind_iff]
    exact ⟨Uf, hUfmem, hWmem⟩
  · rw [show W = withR (W ∘ Sum.inr) (W ∘ Sum.inl) from (Sum.elim_comp_inl_inr W).symm,
        ktapeSem_liftL, Part.mem_map_iff]
    refine ⟨liftWork M₀ A, hUuncompute, ?_⟩
    rw [hWinrEq]

/-! ### Multi-tape reverse leg correctness (conj-5d, reverse) -/

/-- **The designated-pair reverse copy halts on a block source.**  Mirror of
`copyStrAt_output_exists` using `copyStrRev_output_mem`. -/
theorem copyStrAtRev_output_exists {ι' : Type*} [DecidableEq ι'] (s t : ι') (hst : s ≠ t)
    (Y : ι' → Tape Γ) (hblk : IsBlock (Y s)) :
    ∃ W, W ∈ ktapeSem (copyStrAtRev s t hst) CopyState.copy Y := by
  obtain ⟨n, hblock, hout⟩ := hblk
  rw [copyStrAtRev, ktapeSem_renameBank,
    show (fun i => Y (selEquiv s t hst i))
        = withR ((fun i => Y (selEquiv s t hst i)) ∘ Sum.inr)
            (fun i => Y (selEquiv s t hst (Sum.inl i))) from
        (Sum.elim_comp_inl_inr (fun i => Y (selEquiv s t hst i))).symm,
    ktapeSem_liftL]
  exact ⟨_, (Part.mem_map_iff _).mpr ⟨_, (Part.mem_map_iff _).mpr
    ⟨_, copyStrRev_output_mem n (fun i => Y (selEquiv s t hst (Sum.inl i)))
        (by intro i hi
            show (Y (selEquiv s t hst (Sum.inl (Sum.inl ())))).nth i ≠ default
            rw [selEquiv_inl_inl]; exact hblock i hi)
        (by show (Y (selEquiv s t hst (Sum.inl (Sum.inl ())))).nth (n : ℤ) = default
            rw [selEquiv_inl_inl]; exact hout (n : ℤ) (by omega))
        (by show (Y (selEquiv s t hst (Sum.inl (Sum.inl ())))).nth (-1) = default
            rw [selEquiv_inl_inl]; exact hout (-1) (by omega)),
      rfl⟩, rfl⟩⟩

/-- **The reverse copy fold halts on block sources.**  Reverse nesting: the tail runs
first, then the head's reverse copy (whose source is preserved by the tail). -/
theorem copyPairsRev_output_exists {ι' : Type*} [DecidableEq ι'] :
    (l : List {p : ι' × ι' // p.1 ≠ p.2}) → (X : ι' → Tape Γ) →
    (∀ p ∈ l, IsBlock (X p.1.1)) →
    l.Pairwise (fun p q => p.1.1 ≠ q.1.2 ∧ p.1.2 ≠ q.1.2) →
    ∃ V, V ∈ ktapeSem (copyPairsRev l) (foldStartRev l) X
  | [], X, _, _ => ⟨X, by
      show X ∈ ktapeSem (haltMachine (Γ := Γ) (ι' := ι')) () X
      rw [ktapeSem_haltMachine]; exact Part.mem_some X⟩
  | p₀ :: rest, X, hsrc, hpw => by
      obtain ⟨hpwhead, hpwrest⟩ := List.pairwise_cons.mp hpw
      obtain ⟨W, hW⟩ :=
        copyPairsRev_output_exists rest X (fun q hq => hsrc q (by simp [hq])) hpwrest
      have hWsrc : W p₀.1.1 = X p₀.1.1 :=
        copyPairsRev_preserves rest X W (fun q hq => hsrc q (by simp [hq])) hpwrest hW
          p₀.1.1 (fun q hq => (hpwhead q hq).1)
      obtain ⟨V, hVc⟩ := copyStrAtRev_output_exists p₀.1.1 p₀.1.2 p₀.2 W
        (by rw [hWsrc]; exact hsrc p₀ (by simp))
      refine ⟨V, ?_⟩
      have hVm : V ∈ (ktapeSem (copyPairsRev rest) (foldStartRev rest) X).bind
          (ktapeSem (copyStrAtRev p₀.1.1 p₀.1.2 p₀.2) CopyState.copy) :=
        Part.mem_bind_iff.mpr ⟨W, hW, hVc⟩
      rw [← ktapeSem_seq] at hVm
      exact hVm

/-- **The multi-tape reverse copy halts on block work tapes.** -/
theorem copyMultiKRev_output_exists (k : ℕ) (X : ((Fin k ⊕ Fin 1) ⊕ Fin k) → Tape Γ)
    (hsrc : ∀ j, IsBlock (X (Sum.inl (Sum.inl j)))) :
    ∃ W, W ∈ ktapeSem (copyMultiKRev k) (foldStartRev (tapePairs k)) X := by
  refine copyPairsRev_output_exists (tapePairs k) X ?_ ?_
  · intro p hp; rw [tapePairs, List.mem_ofFn] at hp; obtain ⟨i, rfl⟩ := hp; exact hsrc i
  · rw [tapePairs, List.pairwise_ofFn]
    intro a b hab
    refine ⟨by simp [tapePair], ?_⟩
    simp only [tapePair, ne_eq, Sum.inr.injEq]; exact Fin.ne_of_lt hab

/-- **The multi-tape reverse copy preserves the work⊕history banks.** -/
theorem copyMultiKRev_preserves_left (k : ℕ) (X V : ((Fin k ⊕ Fin 1) ⊕ Fin k) → Tape Γ)
    (hsrc : ∀ j, IsBlock (X (Sum.inl (Sum.inl j))))
    (hV : V ∈ ktapeSem (copyMultiKRev k) (foldStartRev (tapePairs k)) X) :
    ∀ b : Fin k ⊕ Fin 1, V (Sum.inl b) = X (Sum.inl b) := by
  intro b
  refine copyPairsRev_preserves (tapePairs k) X V ?_ ?_ hV (Sum.inl b) ?_
  · intro p hp; rw [tapePairs, List.mem_ofFn] at hp; obtain ⟨i, rfl⟩ := hp; exact hsrc i
  · rw [tapePairs, List.pairwise_ofFn]
    intro a c hac
    refine ⟨by simp [tapePair], ?_⟩
    simp only [tapePair, ne_eq, Sum.inr.injEq]; exact Fin.ne_of_lt hac
  · intro p hp; rw [tapePairs, List.mem_ofFn] at hp; obtain ⟨i, rfl⟩ := hp; simp [tapePair]

/-- **The multi-tape reverse leg `B'` blanks the (block) ancillas and restores work.**
Multi-tape analogue of `bennettBStr'_blanks`: on a work block `liftWork U` (with `M₀`
mapping `U` to block tapes `T`) and ancillas `S` holding the lift of `T`, `B'` blanks
all ancillas and uncomputes the work back to `liftWork U`. -/
theorem bennettBStrK'_blanks (k : ℕ) (M₀ : KMachine Γ Λ (Fin k)) (q₀ : Λ)
    (U T : Fin k → Tape Γ) (hUT : T ∈ ktapeSem M₀ q₀ U) (hTblk : ∀ j, IsBlock (T j))
    (S : Fin k → Tape (BennettAlph2 Γ Λ (Fin k)))
    (hS : ∀ j, S j = Tape.map inlMap (T j)) :
    withR (fun _ : Fin k => (default : Tape (BennettAlph2 Γ Λ (Fin k)))) (liftWork M₀ U)
      ∈ ktapeSem (bennettBStrK' k M₀) (Sum.inl (BennettState2.A1 q₀))
          (withR S (liftWork M₀ U)) := by
  classical
  obtain ⟨Y, hY, hYwork⟩ := phaseF2_forward_correct M₀ q₀ U T hUT
  set Uf : (Fin k ⊕ Fin 1) ⊕ Fin k → Tape (BennettAlph2 Γ Λ (Fin k)) :=
    withR S Y with hUf
  have hUfmem : Uf ∈ ktapeSem (liftL (phaseF2 M₀) (κ := Fin k)) (BennettState2.A1 q₀)
      (withR S (liftWork M₀ U)) := by
    rw [ktapeSem_liftL, Part.mem_map_iff]; exact ⟨Y, hY, rfl⟩
  have hblkUf : ∀ j, IsBlock (Uf (Sum.inl (Sum.inl j))) := by
    intro j; show IsBlock (Y (Sum.inl j)); rw [hYwork j]; exact isBlock_map (hTblk j)
  have htgtUf : ∀ j, Uf (Sum.inr j) = Uf (Sum.inl (Sum.inl j)) := by
    intro j; show S j = Y (Sum.inl j); rw [hS j, hYwork j]
  obtain ⟨W, hWmem⟩ := copyMultiKRev_output_exists k Uf hblkUf
  have hWinlY : W ∘ Sum.inl = Y := by
    funext x; show W (Sum.inl x) = Y x
    rw [copyMultiKRev_preserves_left k Uf W hblkUf hWmem x]; rfl
  have hWinr : ∀ j, W (Sum.inr j) = default :=
    copyMultiKRev_blanks k Uf W hblkUf htgtUf hWmem
  have hUuncompute : liftWork M₀ U ∈
      ktapeSem (phaseU2 M₀) UncompState.RStart (W ∘ Sum.inl) := by
    rw [hWinlY]
    exact (phaseF2_semInverse M₀ q₀).fwd (liftWork M₀ U) Y (liftWork_WFblank M₀ U) hY
  have hanc : (fun _ : Fin k => (default : Tape (BennettAlph2 Γ Λ (Fin k)))) = W ∘ Sum.inr := by
    funext j; exact (hWinr j).symm
  rw [bennettBStrK', ktapeSem_seq, Part.mem_bind_iff]
  refine ⟨Uf, hUfmem, ?_⟩
  rw [ktapeSem_seq, Part.mem_bind_iff]
  refine ⟨W, hWmem, ?_⟩
  rw [show W = withR (W ∘ Sum.inr) (W ∘ Sum.inl) from (Sum.elim_comp_inl_inr W).symm,
      ktapeSem_liftL, Part.mem_map_iff]
  refine ⟨liftWork M₀ U, hUuncompute, ?_⟩
  rw [← hanc]

/-! ### The multi-tape Bennett involution `D_K = B ; swap ; B'` (conj-5e) -/

/-- The multi-tape Bennett involution machine
`bennettBStrK ; swap ; bennettBStrK'`. -/
noncomputable def bennettBStrKD (k : ℕ) (M₀ : KMachine Γ Λ (Fin k)) (q₀ : Λ) :=
  seq (seq (bennettBStrK k M₀) (bankSwap (wAncSwap (ι := Fin k))) false) (bennettBStrK' k M₀)
      (Sum.inl (BennettState2.A1 q₀))

/-- **`D_K` simulates `M₀` on multi-tape block involutive points.**  Multi-tape
analogue of `bennettBStrD_simulates`: for block tapes `A`, `U` with `M₀ A = U` and
`M₀ U = A`, `D_K` maps `enc A` to `enc U`.  Chains `bennettBStrK_correct_full` (B) →
work↔ancilla swap → `bennettBStrK'_blanks` (B', ancillas hold `lift A`). -/
theorem bennettBStrKD_simulates (k : ℕ) (M₀ : KMachine Γ Λ (Fin k)) (q₀ : Λ)
    (A U : Fin k → Tape Γ) (hA : ∀ j, IsBlock (A j)) (hU : ∀ j, IsBlock (U j))
    (hAU : U ∈ ktapeSem M₀ q₀ A) (hUA : A ∈ ktapeSem M₀ q₀ U) :
    withR (fun _ : Fin k => (default : Tape (BennettAlph2 Γ Λ (Fin k)))) (liftWork M₀ U)
      ∈ ktapeSem (bennettBStrKD k M₀ q₀)
          (Sum.inl (Sum.inl (Sum.inl (Sum.inl (BennettState2.A1 q₀)))))
          (withR (fun _ : Fin k => (default : Tape (BennettAlph2 Γ Λ (Fin k)))) (liftWork M₀ A)) := by
  classical
  have hB := bennettBStrK_correct_full k M₀ q₀ A U hU hAU
  set ZB : (Fin k ⊕ Fin 1) ⊕ Fin k → Tape (BennettAlph2 Γ Λ (Fin k)) :=
    withR (fun j => liftWork M₀ U (Sum.inl j)) (liftWork M₀ A) with hZB
  set VB : (Fin k ⊕ Fin 1) ⊕ Fin k → Tape (BennettAlph2 Γ Λ (Fin k)) :=
    withR (fun j => liftWork M₀ A (Sum.inl j)) (liftWork M₀ U) with hVB
  have hswap : VB ∈ ktapeSem (bankSwap (wAncSwap (ι := Fin k))) false ZB := by
    have hstep : kstep (bankSwap (wAncSwap (ι := Fin k)) (Γ := BennettAlph2 Γ Λ (Fin k)))
        ⟨false, ZB⟩ = some ⟨true, (KStmt.perm (wAncSwap (ι := Fin k))).apply ZB⟩ := by
      simp [kstep, bankSwap]
    have hhalt : kstep (bankSwap (wAncSwap (ι := Fin k)) (Γ := BennettAlph2 Γ Λ (Fin k)))
        (⟨true, (KStmt.perm (wAncSwap (ι := Fin k))).apply ZB⟩ :
          KCfg (BennettAlph2 Γ Λ (Fin k)) Bool ((Fin k ⊕ Fin 1) ⊕ Fin k)) = none := by
      simp [kstep, bankSwap]
    have hVBeq : VB = (KStmt.perm (wAncSwap (ι := Fin k))).apply ZB := by
      funext i
      show VB i = ZB ((wAncSwap (ι := Fin k))⁻¹ i)
      rw [wAncSwap_selfInverse]
      rcases i with (j | h) | j <;> rfl
    rw [hVBeq]
    exact (Part.mem_map_iff _).mpr
      ⟨⟨true, (KStmt.perm (wAncSwap (ι := Fin k))).apply ZB⟩,
        StateTransition.mem_eval.mpr
          ⟨Relation.ReflTransGen.single (Option.mem_def.mpr hstep), hhalt⟩, rfl⟩
  have hBp := bennettBStrK'_blanks k M₀ q₀ U A hUA hA
    (fun j => liftWork M₀ A (Sum.inl j)) (fun _ => rfl)
  rw [bennettBStrKD, ktapeSem_seq, Part.mem_bind_iff]
  refine ⟨VB, ?_, hBp⟩
  rw [ktapeSem_seq, Part.mem_bind_iff]
  exact ⟨ZB, hB, hswap⟩

/-- **Multi-tape block-data unconditional symmetrisation.**  The `k`-tape analogue of
`nakano_symmetrisation_strvalued`: for any `M₀` computing a partial involution on
block-data `k`-tape configurations and preserving blockness, `D_K = B ; swap ; B'`
simulates `M₀` and is involutive on the encoded points, with no `KReversible`
hypothesis on `M₀`. -/
theorem nakano_symmetrisation_strvalued_K (k : ℕ) (M₀ : KMachine Γ Λ (Fin k)) (q₀ : Λ)
    (hInvol : ∀ X Y, Y ∈ ktapeSem M₀ q₀ X → X ∈ ktapeSem M₀ q₀ Y)
    (hblk : ∀ X Y, (∀ j, IsBlock (X j)) → Y ∈ ktapeSem M₀ q₀ X → ∀ j, IsBlock (Y j)) :
    ∃ (q0' : _)
      (enc : (Fin k → Tape Γ) →
        ((Fin k ⊕ Fin 1) ⊕ Fin k → Tape (BennettAlph2 Γ Λ (Fin k)))),
      ∀ A U, (∀ j, IsBlock (A j)) → U ∈ ktapeSem M₀ q₀ A →
        enc U ∈ ktapeSem (bennettBStrKD k M₀ q₀) q0' (enc A) ∧
        enc A ∈ ktapeSem (bennettBStrKD k M₀ q₀) q0' (enc U) := by
  refine ⟨Sum.inl (Sum.inl (Sum.inl (Sum.inl (BennettState2.A1 q₀)))),
    (fun A => withR (fun _ : Fin k => (default : Tape (BennettAlph2 Γ Λ (Fin k))))
      (liftWork M₀ A)), ?_⟩
  intro A U hA hAU
  have hU : ∀ j, IsBlock (U j) := hblk A U hA hAU
  have hUA : A ∈ ktapeSem M₀ q₀ U := hInvol A U hAU
  exact ⟨bennettBStrKD_simulates k M₀ q₀ A U hA hU hAU hUA,
         bennettBStrKD_simulates k M₀ q₀ U A hU hA hUA hAU⟩

/-- **`bennettBStrD` computes a partial involution** (the paper's central predicate
`IsPartialInvolutionOn`) on the encoded block involutive points.  Block-data analogue
of `bennettD_isPartialInvolutionOn`. -/
theorem bennettBStrD_isPartialInvolutionOn (M₀ : KMachine Γ Λ Unit) (q₀ : Λ) :
    IsPartialInvolutionOn (bennettBStrD M₀ q₀)
      (Sum.inl (Sum.inl (Sum.inl (Sum.inl (BennettState2.A1 q₀)))))
      (fun X => ∃ A U, (∀ j, IsBlock (A j)) ∧ (∀ j, IsBlock (U j)) ∧
        U ∈ ktapeSem M₀ q₀ A ∧ A ∈ ktapeSem M₀ q₀ U ∧
        X = withR (fun _ : Unit => (default : Tape (BennettAlph2 Γ Λ Unit)))
          (liftWork M₀ A)) := by
  rintro X Y ⟨A, U, hA, hU, hAU, hUA, rfl⟩ hY
  have h1 := bennettBStrD_simulates M₀ q₀ A U hA hU hAU hUA
  have h2 := bennettBStrD_simulates M₀ q₀ U A hU hA hUA hAU
  rw [Part.mem_unique hY h1]; exact h2

/-- **`bennettBStrKD` computes a partial involution** on the encoded multi-tape block
involutive points.  Multi-tape analogue of `bennettD_isPartialInvolutionOn`. -/
theorem bennettBStrKD_isPartialInvolutionOn (k : ℕ) (M₀ : KMachine Γ Λ (Fin k)) (q₀ : Λ) :
    IsPartialInvolutionOn (bennettBStrKD k M₀ q₀)
      (Sum.inl (Sum.inl (Sum.inl (Sum.inl (BennettState2.A1 q₀)))))
      (fun X => ∃ A U, (∀ j, IsBlock (A j)) ∧ (∀ j, IsBlock (U j)) ∧
        U ∈ ktapeSem M₀ q₀ A ∧ A ∈ ktapeSem M₀ q₀ U ∧
        X = withR (fun _ : Fin k => (default : Tape (BennettAlph2 Γ Λ (Fin k))))
          (liftWork M₀ A)) := by
  rintro X Y ⟨A, U, hA, hU, hAU, hUA, rfl⟩ hY
  have h1 := bennettBStrKD_simulates k M₀ q₀ A U hA hU hAU hUA
  have h2 := bennettBStrKD_simulates k M₀ q₀ U A hU hA hUA hAU
  rw [Part.mem_unique hY h1]; exact h2

/-! ### Non-vacuity: the block symmetrisation applies to genuine block involutions

The block-data theorems are not vacuous.  A cellwise involution `cellwiseM0 g`
(write `g` to every head) that *fixes the blank* (`g default = default`) preserves
blockness: `g` then maps non-blank to non-blank, so a block stays a block.  Hence
`nakano_symmetrisation_strvalued`/`_K` apply to it on arbitrary block data (the full
block is carried through `D`'s copy leg), with `g` a genuine non-trivial involution. -/

section CellwiseBlock
variable (g : Γ → Γ)

/-- A blank-fixing involution preserves blockness on a single tape: writing `g` to the
head of a block tape yields a block tape. -/
theorem gCell_isBlock (hg : ∀ x, g (g x) = x) (hgdef : g default = default)
    {T : Tape Γ} (h : IsBlock T) : IsBlock (T.write (g T.1)) := by
  obtain ⟨n, hbk, hout⟩ := h
  have hgne : ∀ x : Γ, x ≠ default → g x ≠ default := fun x hx hgx =>
    hx (by rw [← hg x, hgx, hgdef])
  have hT1 : T.1 = T.nth 0 := rfl
  refine ⟨n, ?_, ?_⟩
  · intro i hi
    rw [Tape.write_nth]
    by_cases hi0 : (i : ℤ) = 0
    · rw [if_pos hi0, hT1]
      apply hgne
      have hb := hbk i hi
      rwa [hi0] at hb
    · rw [if_neg hi0]; exact hbk i hi
  · intro m hm
    rw [Tape.write_nth]
    by_cases hm0 : m = 0
    · rw [if_pos hm0, hT1, hout 0 (hm0 ▸ hm)]; exact hgdef
    · rw [if_neg hm0]; exact hout m hm

/-- `cellwiseM0 g` preserves blockness when `g` fixes the blank. -/
theorem cellwiseM0_blockpreserving {ι : Type*} (hg : ∀ x, g (g x) = x)
    (hgdef : g default = default) (X Y : ι → Tape Γ)
    (hX : ∀ j, IsBlock (X j)) (hY : Y ∈ ktapeSem (cellwiseM0 g) false X) :
    ∀ j, IsBlock (Y j) := by
  rw [cellwiseM0_sem] at hY
  subst hY
  intro j
  exact gCell_isBlock g hg hgdef (hX j)

/-- **Non-vacuity (single tape).**  The block symmetrisation applies to every
blank-fixing cellwise involution, on arbitrary block data. -/
theorem cellwiseM0_strvalued (hg : ∀ x, g (g x) = x) (hgdef : g default = default) :
    ∃ (q0' : _) (enc : (Unit → Tape Γ) →
        ((Unit ⊕ Fin 1) ⊕ Unit → Tape (BennettAlph2 Γ Bool Unit))),
      ∀ A U, (∀ j, IsBlock (A j)) → U ∈ ktapeSem (cellwiseM0 g) false A →
        enc U ∈ ktapeSem (bennettBStrD (cellwiseM0 g) false) q0' (enc A) ∧
        enc A ∈ ktapeSem (bennettBStrD (cellwiseM0 g) false) q0' (enc U) :=
  nakano_symmetrisation_strvalued (cellwiseM0 g) false
    (cellwiseM0_involution g hg) (cellwiseM0_blockpreserving g hg hgdef)

/-- **Non-vacuity (multi-tape).**  The `k`-tape block symmetrisation applies to every
blank-fixing cellwise involution. -/
theorem cellwiseM0_strvalued_K (k : ℕ) (hg : ∀ x, g (g x) = x) (hgdef : g default = default) :
    ∃ (q0' : _) (enc : (Fin k → Tape Γ) →
        ((Fin k ⊕ Fin 1) ⊕ Fin k → Tape (BennettAlph2 Γ Bool (Fin k)))),
      ∀ A U, (∀ j, IsBlock (A j)) → U ∈ ktapeSem (cellwiseM0 g) false A →
        enc U ∈ ktapeSem (bennettBStrKD k (cellwiseM0 g) false) q0' (enc A) ∧
        enc A ∈ ktapeSem (bennettBStrKD k (cellwiseM0 g) false) q0' (enc U) :=
  nakano_symmetrisation_strvalued_K k (cellwiseM0 g) false
    (cellwiseM0_involution g hg) (cellwiseM0_blockpreserving g hg hgdef)

end CellwiseBlock

end PeriodicTM
