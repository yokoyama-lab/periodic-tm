/-
# Reversible copy machine (R1 G2 architecture, A-copy)

The Bennett F;C;U wrapper needs a reversible copy of the work output onto a
fresh ancilla.  This file provides the **single-cell** copy `copyM` (one
`KStmt.write` copying the source heads to the target) and its semantic inverse
`copyMrev` (blank the target), validated in `proto/bennett_fcu.py`.

`copyM` is a genuine `SemInverse` of `copyMrev` on the head-level domains
(`DomIn` = target heads blank, `DomOut` = target heads match the source) — the
same domain-restricted reversibility as `phaseF2`/`phaseU2`.  The full-string
(tape-traversal) copy is left for later; single-cell already drives the F;C;U
assembly for head-valued involutions.
-/
import FiniteOrderTM.SemReversible
import FiniteOrderTM.Reindex

namespace PeriodicTM

open Turing

variable {Γ : Type*} [Inhabited Γ] {ι : Type*}

/-- **Semantics of a one-write-then-halt machine.**  If `M` writes `w b` at the
start state `false` (reading heads `b`) and halts at `true`, its tape semantics
from `false` is the single write applied. -/
theorem singleWrite_ktapeSem (M : KMachine Γ Bool ι) (w : (ι → Γ) → (ι → Γ))
    (hstep : ∀ b, M false b = some (true, KStmt.write (w b)))
    (hhalt : ∀ b, M true b = none) (T : ι → Tape Γ) (V : ι → Tape Γ) :
    V ∈ ktapeSem M false T ↔ V = (KStmt.write (w (headsV T))).apply T := by
  have hstep1 : kstep M ⟨false, T⟩ = some ⟨true, (KStmt.write (w (headsV T))).apply T⟩ := by
    simp only [kstep, hstep, Option.map_some]
  have hhalt2 : ∀ X, kstep M (⟨true, X⟩ : KCfg Γ Bool ι) = none := by
    intro X; simp only [kstep, hhalt]; rfl
  constructor
  · intro hV
    obtain ⟨c, hc, rfl⟩ := (Part.mem_map_iff _).mp hV
    obtain ⟨hr, hcfhalt⟩ := StateTransition.mem_eval.mp hc
    rcases Relation.ReflTransGen.cases_head hr with heq | ⟨b, hb, hrest⟩
    · rw [← heq, hstep1] at hcfhalt; exact absurd hcfhalt (by simp)
    · have hbeq : b = (⟨true, (KStmt.write (w (headsV T))).apply T⟩ : KCfg Γ Bool ι) := by
        rw [Option.mem_def, hstep1] at hb; exact (Option.some.inj hb).symm
      subst hbeq
      rcases Relation.ReflTransGen.cases_head hrest with heq2 | ⟨b2, hb2, _⟩
      · exact (congrArg KCfg.tapes heq2).symm
      · rw [Option.mem_def, hhalt2] at hb2; exact absurd hb2 (by simp)
  · intro hV; subst hV
    refine (Part.mem_map_iff _).mpr
      ⟨⟨true, (KStmt.write (w (headsV T))).apply T⟩,
        StateTransition.mem_eval.mpr ⟨?_, hhalt2 _⟩, rfl⟩
    exact Relation.ReflTransGen.single (Option.mem_def.mpr hstep1)

/-- The single-cell copy: write each target bank's head with the corresponding
source bank's head; source banks unchanged. -/
def copyM : KMachine Γ Bool (ι ⊕ ι) := fun q b =>
  match q with
  | false => some (true, KStmt.write (fun i => match i with
      | Sum.inl s => b (Sum.inl s)
      | Sum.inr t => b (Sum.inl t)))
  | true => none

/-- The reverse copy: blank each target bank's head; source banks unchanged. -/
def copyMrev : KMachine Γ Bool (ι ⊕ ι) := fun q b =>
  match q with
  | false => some (true, KStmt.write (fun i => match i with
      | Sum.inl s => b (Sum.inl s)
      | Sum.inr _ => default))
  | true => none

/-- Input domain for `copyM`: every target head is blank. -/
def TargetBlank (T : ι ⊕ ι → Tape Γ) : Prop := ∀ t, (T (Sum.inr t)).1 = default

/-- Output domain for `copyM`: every target head matches its source head. -/
def TargetMatchesSource (T : ι ⊕ ι → Tape Γ) : Prop :=
  ∀ t, (T (Sum.inr t)).1 = (T (Sum.inl t)).1

/-- **A-copy: `copyMrev` is a `SemInverse` of `copyM`.**  Forward leg on
`TargetBlank` inputs, backward leg on `TargetMatchesSource` outputs. -/
theorem copyM_semInverse :
    SemInverse (Γ := Γ) (ι := ι ⊕ ι) copyM copyMrev false false
      TargetBlank TargetMatchesSource where
  fwd := by
    intro X Y hX hY
    rw [singleWrite_ktapeSem copyM _ (fun _ => rfl) (fun _ => rfl)] at hY
    rw [singleWrite_ktapeSem copyMrev _ (fun _ => rfl) (fun _ => rfl)]
    subst hY
    funext i
    cases i with
    | inl s => simp [KStmt.apply, headsV, Tape.write_self]
    | inr t =>
      have h := hX t
      simp only [KStmt.apply, headsV, tape_write_write]
      rw [← h, Tape.write_self]
  bwd := by
    intro X Y hY hX
    rw [singleWrite_ktapeSem copyMrev _ (fun _ => rfl) (fun _ => rfl)] at hX
    rw [singleWrite_ktapeSem copyM _ (fun _ => rfl) (fun _ => rfl)]
    subst hX
    funext i
    cases i with
    | inl s => simp [KStmt.apply, headsV, Tape.write_self]
    | inr t =>
      simp only [KStmt.apply, headsV, tape_write_write]
      have hh : (Y (Sum.inl t)).head = (Y (Sum.inr t)).head := (hY t).symm
      rw [hh]
      exact (Tape.write_self _).symm

/-! ### Copy on the Bennett common bank index

`liftL phaseF2 (κ := ι)` outputs on the bank index `(ι ⊕ Fin 1) ⊕ ι` =
(work ⊕ history) ⊕ ancilla.  The F;C;U wrapper's middle leg copies the *work*
heads onto the *ancilla*, freezing work and history.  `copyWA` is the single-cell
copy on this index (generic in the history bank `τ`): it reuses
`singleWrite_ktapeSem` exactly like `copyM`, so no new machinery is needed. -/

variable {τ : Type*}

/-- Copy work heads onto the ancilla, freezing work+history.  Bank index
`(ι ⊕ τ) ⊕ ι`: `Sum.inl _` is the work⊕history block, `Sum.inr t` the ancilla. -/
def copyWA : KMachine Γ Bool ((ι ⊕ τ) ⊕ ι) := fun q b =>
  match q with
  | false => some (true, KStmt.write (fun i => match i with
      | Sum.inl x => b (Sum.inl x)
      | Sum.inr t => b (Sum.inl (Sum.inl t))))
  | true => none

/-- Reverse: blank the ancilla, freezing work+history. -/
def copyWArev : KMachine Γ Bool ((ι ⊕ τ) ⊕ ι) := fun q b =>
  match q with
  | false => some (true, KStmt.write (fun i => match i with
      | Sum.inl x => b (Sum.inl x)
      | Sum.inr _ => default))
  | true => none

/-- Input domain for `copyWA`: every ancilla head is blank. -/
def AncBlank (T : (ι ⊕ τ) ⊕ ι → Tape Γ) : Prop := ∀ t, (T (Sum.inr t)).1 = default

/-- Output domain for `copyWA`: every ancilla head matches its work head. -/
def AncMatchesWork (T : (ι ⊕ τ) ⊕ ι → Tape Γ) : Prop :=
  ∀ t, (T (Sum.inr t)).1 = (T (Sum.inl (Sum.inl t))).1

/-- **`copyWArev` is a `SemInverse` of `copyWA`** on the Bennett common bank
index.  Same proof shape as `copyM_semInverse`; freezing the history bank is
automatic (the `Sum.inl` case is a no-op write). -/
theorem copyWA_semInverse :
    SemInverse (Γ := Γ) (ι := (ι ⊕ τ) ⊕ ι) copyWA copyWArev false false
      AncBlank AncMatchesWork where
  fwd := by
    intro X Y hX hY
    rw [singleWrite_ktapeSem copyWA _ (fun _ => rfl) (fun _ => rfl)] at hY
    rw [singleWrite_ktapeSem copyWArev _ (fun _ => rfl) (fun _ => rfl)]
    subst hY
    funext i
    cases i with
    | inl x => simp [KStmt.apply, headsV, Tape.write_self]
    | inr t =>
      have h := hX t
      simp only [KStmt.apply, headsV, tape_write_write]
      rw [← h, Tape.write_self]
  bwd := by
    intro X Y hY hX
    rw [singleWrite_ktapeSem copyWArev _ (fun _ => rfl) (fun _ => rfl)] at hX
    rw [singleWrite_ktapeSem copyWA _ (fun _ => rfl) (fun _ => rfl)]
    subst hX
    funext i
    cases i with
    | inl x => simp [KStmt.apply, headsV, Tape.write_self]
    | inr t =>
      simp only [KStmt.apply, headsV, tape_write_write]
      have hh : (Y (Sum.inl (Sum.inl t))).head = (Y (Sum.inr t)).head := (hY t).symm
      rw [hh]
      exact (Tape.write_self _).symm

/-- `copyWA` freezes the work+history block (`Sum.inl`). -/
theorem copyWA_preserves_left {Y V : (ι ⊕ τ) ⊕ ι → Tape Γ}
    (h : V ∈ ktapeSem (copyWA (Γ := Γ) (ι := ι) (τ := τ)) false Y) :
    ∀ x, V (Sum.inl x) = Y (Sum.inl x) := by
  rw [singleWrite_ktapeSem copyWA _ (fun _ => rfl) (fun _ => rfl)] at h
  subst h
  intro x
  simp [KStmt.apply, headsV, Tape.write_self]

/-- `copyWA`'s output matches the ancilla to the work head (`AncMatchesWork`). -/
theorem copyWA_anc {Y V : (ι ⊕ τ) ⊕ ι → Tape Γ}
    (h : V ∈ ktapeSem (copyWA (Γ := Γ) (ι := ι) (τ := τ)) false Y) :
    AncMatchesWork V := by
  rw [singleWrite_ktapeSem copyWA _ (fun _ => rfl) (fun _ => rfl)] at h
  subst h
  intro t
  rfl

/-- `copyWA`'s exact ancilla output: each ancilla cell is the old ancilla cell
with its head overwritten by the work head. -/
theorem copyWA_anc_full {Y V : (ι ⊕ τ) ⊕ ι → Tape Γ}
    (h : V ∈ ktapeSem (copyWA (Γ := Γ) (ι := ι) (τ := τ)) false Y) :
    ∀ j, V (Sum.inr j) = (Y (Sum.inr j)).write (Y (Sum.inl (Sum.inl j))).1 := by
  rw [singleWrite_ktapeSem copyWA _ (fun _ => rfl) (fun _ => rfl)] at h
  subst h
  intro j
  rfl

/-- `copyWArev` freezes the work+history block (`Sum.inl`). -/
theorem copyWArev_preserves_left {Y V : (ι ⊕ τ) ⊕ ι → Tape Γ}
    (h : V ∈ ktapeSem (copyWArev (Γ := Γ) (ι := ι) (τ := τ)) false Y) :
    ∀ x, V (Sum.inl x) = Y (Sum.inl x) := by
  rw [singleWrite_ktapeSem copyWArev _ (fun _ => rfl) (fun _ => rfl)] at h
  subst h
  intro x
  simp [KStmt.apply, headsV, Tape.write_self]

/-- `copyWArev` blanks the ancilla, *provided* each ancilla cell is single-cell
(blank except its head) — then writing the blank head fully blanks it. -/
theorem copyWArev_blanks {Y V : (ι ⊕ τ) ⊕ ι → Tape Γ}
    (h : V ∈ ktapeSem (copyWArev (Γ := Γ) (ι := ι) (τ := τ)) false Y)
    (hY : ∀ j, Y (Sum.inr j) = (default : Tape Γ).write (Y (Sum.inr j)).1) :
    ∀ j, V (Sum.inr j) = default := by
  rw [singleWrite_ktapeSem copyWArev _ (fun _ => rfl) (fun _ => rfl)] at h
  subst h
  intro j
  show (Y (Sum.inr j)).write default = default
  rw [hY j, tape_write_write]
  exact Tape.write_self default

/-- **Test for `SemInverse.liftL`.**  Lifting the single-cell copy onto a larger
bank index (`(ι ⊕ ι) ⊕ κ`, with `κ` a frozen extra bank) keeps the
semantic-inverse relation; the lifted domains constrain only the copy banks. -/
example {κ : Type*} :
    SemInverse (Γ := Γ) (liftL copyM (κ := κ)) (liftL copyMrev (κ := κ)) false false
      (fun U : (ι ⊕ ι) ⊕ κ → Tape Γ => TargetBlank (U ∘ Sum.inl))
      (fun U : (ι ⊕ ι) ⊕ κ → Tape Γ => TargetMatchesSource (U ∘ Sum.inl)) :=
  copyM_semInverse.liftL

/-! ### Full-string traversal copy (Option A, definition)

The single-cell `copyWA` only duplicates the head, closing the unconditional
theorem for head-valued data.  `copyStr` is the reversible full-string copy
(prototype: `proto/copy_str.py`): a head-traversal machine that walks the source
string left-to-right writing each cell onto the (blank) target, detects the right
end by the terminating blank, then sweeps back home.  Domain: a blank-free
contiguous block anchored at home (an internal blank is read as the end).

This commit lands the machine definition and its structural single-step lemmas;
the traversal run-semantics (`reachesN` induction) and `SemInverse` are the
next, large step (cf. `phaseF2_forward_sim`). -/

/-- A tape is determined by its `nth` function. -/
theorem tape_ext_nth {T₁ T₂ : Tape Γ} (h : ∀ i : ℤ, T₁.nth i = T₂.nth i) : T₁ = T₂ := by
  obtain ⟨h1, l1, r1⟩ := T₁
  obtain ⟨h2, l2, r2⟩ := T₂
  have hh : h1 = h2 := by have h0 := h 0; simpa [Tape.nth] using h0
  have hr : r1 = r2 := ListBlank.ext fun n => by
    have := h (n + 1); simpa [Tape.nth] using this
  have hl : l1 = l2 := ListBlank.ext fun n => by
    have := h (Int.negSucc n); simpa [Tape.nth] using this
  subst hh; subst hl; subst hr; rfl

section CopyStr
variable [DecidableEq Γ]

/-- States of the full-string copy: `copy` (decide/write at a cell), `copyMove`
(advance right), `ret` (sweep back left), `done` (halt). -/
inductive CopyState
  | copy | copyMove | ret | done
  deriving DecidableEq, Inhabited

open CopyState in
/-- Forward full-string copy on `Unit ⊕ Unit` (source `inl`, target `inr`). -/
def copyStr : KMachine Γ CopyState (Unit ⊕ Unit) := fun q b =>
  match q with
  | copy =>
      if b (Sum.inl ()) = default then
        some (ret, KStmt.move (fun _ => some Dir.left))
      else
        some (copyMove, KStmt.write (fun _ => b (Sum.inl ())))
  | copyMove => some (copy, KStmt.move (fun _ => some Dir.right))
  | ret =>
      if b (Sum.inl ()) = default then
        some (done, KStmt.move (fun _ => some Dir.right))
      else
        some (ret, KStmt.move (fun _ => some Dir.left))
  | done => none

open CopyState in
/-- Reverse full-string copy: same traversal, but blank the target cell (unwrite)
instead of copying.  Inverse of `copyStr` on `{target blank}`. -/
def copyStrRev : KMachine Γ CopyState (Unit ⊕ Unit) := fun q b =>
  match q with
  | copy =>
      if b (Sum.inl ()) = default then
        some (ret, KStmt.move (fun _ => some Dir.left))
      else
        some (copyMove, KStmt.write (fun i => match i with
          | Sum.inl _ => b (Sum.inl ())
          | Sum.inr _ => default))
  | copyMove => some (copy, KStmt.move (fun _ => some Dir.right))
  | ret =>
      if b (Sum.inl ()) = default then
        some (done, KStmt.move (fun _ => some Dir.right))
      else
        some (ret, KStmt.move (fun _ => some Dir.left))
  | done => none

@[simp] theorem copyStr_done (b) : copyStr (Γ := Γ) CopyState.done b = none := rfl

@[simp] theorem copyStr_copyMove (b) :
    copyStr (Γ := Γ) CopyState.copyMove b
      = some (CopyState.copy, KStmt.move (fun _ => some Dir.right)) := rfl

@[simp] theorem copyStrRev_done (b) : copyStrRev (Γ := Γ) CopyState.done b = none := rfl

@[simp] theorem copyStrRev_copyMove (b) :
    copyStrRev (Γ := Γ) CopyState.copyMove b
      = some (CopyState.copy, KStmt.move (fun _ => some Dir.right)) := rfl

/-! #### Config-level single steps (induction building blocks for the run semantics) -/

theorem copyStr_step_copy_blank {T : Unit ⊕ Unit → Tape Γ}
    (h : (T (Sum.inl ())).1 = default) :
    kstep copyStr ⟨CopyState.copy, T⟩
      = some ⟨CopyState.ret, (KStmt.move (fun _ => some Dir.left)).apply T⟩ := by
  simp [kstep, copyStr, headsV, h]

theorem copyStr_step_copy_write {T : Unit ⊕ Unit → Tape Γ}
    (h : (T (Sum.inl ())).1 ≠ default) :
    kstep copyStr ⟨CopyState.copy, T⟩
      = some ⟨CopyState.copyMove,
          (KStmt.write (fun _ => (T (Sum.inl ())).1)).apply T⟩ := by
  simp [kstep, copyStr, headsV, h]

theorem copyStr_step_copyMove (T : Unit ⊕ Unit → Tape Γ) :
    kstep copyStr ⟨CopyState.copyMove, T⟩
      = some ⟨CopyState.copy, (KStmt.move (fun _ => some Dir.right)).apply T⟩ := by
  simp [kstep, copyStr]

theorem copyStr_step_ret_blank {T : Unit ⊕ Unit → Tape Γ}
    (h : (T (Sum.inl ())).1 = default) :
    kstep copyStr ⟨CopyState.ret, T⟩
      = some ⟨CopyState.done, (KStmt.move (fun _ => some Dir.right)).apply T⟩ := by
  simp [kstep, copyStr, headsV, h]

theorem copyStr_step_ret_move {T : Unit ⊕ Unit → Tape Γ}
    (h : (T (Sum.inl ())).1 ≠ default) :
    kstep copyStr ⟨CopyState.ret, T⟩
      = some ⟨CopyState.ret, (KStmt.move (fun _ => some Dir.left)).apply T⟩ := by
  simp [kstep, copyStr, headsV, h]

theorem copyStr_step_done (T : Unit ⊕ Unit → Tape Γ) :
    kstep copyStr ⟨CopyState.done, T⟩ = none := by simp [kstep, copyStr]

theorem copyStrRev_step_copy_blank {T : Unit ⊕ Unit → Tape Γ}
    (h : (T (Sum.inl ())).1 = default) :
    kstep copyStrRev ⟨CopyState.copy, T⟩
      = some ⟨CopyState.ret, (KStmt.move (fun _ => some Dir.left)).apply T⟩ := by
  simp [kstep, copyStrRev, headsV, h]

theorem copyStrRev_step_copy_write {T : Unit ⊕ Unit → Tape Γ}
    (h : (T (Sum.inl ())).1 ≠ default) :
    kstep copyStrRev ⟨CopyState.copy, T⟩
      = some ⟨CopyState.copyMove,
          (KStmt.write (fun i => match i with
            | Sum.inl _ => (T (Sum.inl ())).1 | Sum.inr _ => default)).apply T⟩ := by
  simp [kstep, copyStrRev, headsV, h]

theorem copyStrRev_step_copyMove (T : Unit ⊕ Unit → Tape Γ) :
    kstep copyStrRev ⟨CopyState.copyMove, T⟩
      = some ⟨CopyState.copy, (KStmt.move (fun _ => some Dir.right)).apply T⟩ := by
  simp [kstep, copyStrRev]

theorem copyStrRev_step_ret_blank {T : Unit ⊕ Unit → Tape Γ}
    (h : (T (Sum.inl ())).1 = default) :
    kstep copyStrRev ⟨CopyState.ret, T⟩
      = some ⟨CopyState.done, (KStmt.move (fun _ => some Dir.right)).apply T⟩ := by
  simp [kstep, copyStrRev, headsV, h]

theorem copyStrRev_step_ret_move {T : Unit ⊕ Unit → Tape Γ}
    (h : (T (Sum.inl ())).1 ≠ default) :
    kstep copyStrRev ⟨CopyState.ret, T⟩
      = some ⟨CopyState.ret, (KStmt.move (fun _ => some Dir.left)).apply T⟩ := by
  simp [kstep, copyStrRev, headsV, h]

theorem copyStrRev_step_done (T : Unit ⊕ Unit → Tape Γ) :
    kstep copyStrRev ⟨CopyState.done, T⟩ = none := by simp [kstep, copyStrRev]

/-! #### One-cell macros (inductive-step unit for the forward sweep) -/

/-- One forward copy step: at a non-blank source cell, write it onto the target
and advance both heads right, returning to `copy`.  Two `kstep`s. -/
theorem copyStr_macro {T : Unit ⊕ Unit → Tape Γ} (h : (T (Sum.inl ())).1 ≠ default) :
    StateTransition.Reaches (kstep copyStr) ⟨CopyState.copy, T⟩
      ⟨CopyState.copy, (KStmt.move (fun _ => some Dir.right)).apply
        ((KStmt.write (fun _ => (T (Sum.inl ())).1)).apply T)⟩ :=
  Relation.ReflTransGen.head (Option.mem_def.mpr (copyStr_step_copy_write h))
    (Relation.ReflTransGen.head (Option.mem_def.mpr (copyStr_step_copyMove _))
      Relation.ReflTransGen.refl)

/-- One reverse copy step: at a non-blank source cell, blank the target and
advance both heads right, returning to `copy`. -/
theorem copyStrRev_macro {T : Unit ⊕ Unit → Tape Γ} (h : (T (Sum.inl ())).1 ≠ default) :
    StateTransition.Reaches (kstep copyStrRev) ⟨CopyState.copy, T⟩
      ⟨CopyState.copy, (KStmt.move (fun _ => some Dir.right)).apply
        ((KStmt.write (fun i => match i with
          | Sum.inl _ => (T (Sum.inl ())).1 | Sum.inr _ => default)).apply T)⟩ :=
  Relation.ReflTransGen.head (Option.mem_def.mpr (copyStrRev_step_copy_write h))
    (Relation.ReflTransGen.head (Option.mem_def.mpr (copyStrRev_step_copyMove _))
      Relation.ReflTransGen.refl)

/-! #### Forward sweep -/

/-- The tape after `n` forward copy macros from `⟨copy, T⟩`. -/
def sweepTape : ℕ → (Unit ⊕ Unit → Tape Γ) → (Unit ⊕ Unit → Tape Γ)
  | 0, T => T
  | (n + 1), T => sweepTape n ((KStmt.move (fun _ => some Dir.right)).apply
      ((KStmt.write (fun _ => (T (Sum.inl ())).1)).apply T))

/-- **Forward sweep.**  Over a length-`n` non-blank source block (cells `0..n-1`),
`copyStr` runs `n` copy macros and reaches `⟨copy, sweepTape n T⟩` (source head now
at the terminating blank).  Induction on `n`, iterating `copyStr_macro`. -/
theorem copyStr_forward_sweep (n : ℕ) : ∀ (T : Unit ⊕ Unit → Tape Γ),
    (∀ i : ℕ, i < n → (T (Sum.inl ())).nth i ≠ default) →
    StateTransition.Reaches (kstep copyStr) ⟨CopyState.copy, T⟩
      ⟨CopyState.copy, sweepTape n T⟩ := by
  induction n with
  | zero => intro T _; exact Relation.ReflTransGen.refl
  | succ n ih =>
    intro T hblock
    have h0 : (T (Sum.inl ())).1 ≠ default := by
      have h := hblock 0 (Nat.succ_pos n); simpa using h
    have hsrc : ∀ i : ℤ, (((KStmt.move (fun _ => some Dir.right)).apply
        ((KStmt.write (fun _ => (T (Sum.inl ())).1)).apply T)) (Sum.inl ())).nth i
        = (T (Sum.inl ())).nth (i + 1) := by
      intro i
      show (((T (Sum.inl ())).write ((T (Sum.inl ())).1)).move Dir.right).nth i
          = (T (Sum.inl ())).nth (i + 1)
      rw [Tape.write_self]
      exact Tape.move_right_nth _ i
    have hblock1 : ∀ i : ℕ, i < n → (((KStmt.move (fun _ => some Dir.right)).apply
        ((KStmt.write (fun _ => (T (Sum.inl ())).1)).apply T)) (Sum.inl ())).nth i ≠ default := by
      intro i hi
      rw [hsrc i, show ((i : ℤ) + 1) = ((i + 1 : ℕ) : ℤ) by push_cast; ring]
      exact hblock (i + 1) (by omega)
    exact (copyStr_macro h0).trans (ih _ hblock1)

/-- One macro shifts the source `nth` index by one. -/
theorem sweepOne_src_nth (T : Unit ⊕ Unit → Tape Γ) (i : ℤ) :
    (((KStmt.move (fun _ => some Dir.right)).apply
      ((KStmt.write (fun _ => (T (Sum.inl ())).1)).apply T)) (Sum.inl ())).nth i
      = (T (Sum.inl ())).nth (i + 1) := by
  show (((T (Sum.inl ())).write ((T (Sum.inl ())).1)).move Dir.right).nth i
      = (T (Sum.inl ())).nth (i + 1)
  rw [Tape.write_self]
  exact Tape.move_right_nth _ i

/-- After `n` forward macros the source head reads the original cell `n`. -/
theorem sweepTape_src_head (n : ℕ) : ∀ T : Unit ⊕ Unit → Tape Γ,
    (sweepTape n T (Sum.inl ())).1 = (T (Sum.inl ())).nth n := by
  induction n with
  | zero => intro T; simp [sweepTape, Tape.nth_zero]
  | succ n ih =>
    intro T
    rw [sweepTape, ih, sweepOne_src_nth,
      show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring]

/-- **Forward sweep to `ret`.**  Over a length-`n` non-blank block terminated by a
blank at cell `n`, `copyStr` reaches `⟨ret, (move L)(sweepTape n T)⟩` (the copy is
done; the return sweep begins). -/
theorem copyStr_forward_to_ret (n : ℕ) (T : Unit ⊕ Unit → Tape Γ)
    (hblock : ∀ i : ℕ, i < n → (T (Sum.inl ())).nth i ≠ default)
    (hend : (T (Sum.inl ())).nth n = default) :
    StateTransition.Reaches (kstep copyStr) ⟨CopyState.copy, T⟩
      ⟨CopyState.ret, (KStmt.move (fun _ => some Dir.left)).apply (sweepTape n T)⟩ := by
  refine (copyStr_forward_sweep n T hblock).trans ?_
  have hb : (sweepTape n T (Sum.inl ())).1 = default := by
    rw [sweepTape_src_head]; exact hend
  exact Relation.ReflTransGen.head
    (Option.mem_def.mpr (copyStr_step_copy_blank hb)) Relation.ReflTransGen.refl

/-! #### Return sweep -/

/-- The tape at `done` after the return sweep from `⟨ret, S⟩` over `k` non-blank
cells leftward (`k` left moves, then one right move home). -/
def retTape : ℕ → (Unit ⊕ Unit → Tape Γ) → (Unit ⊕ Unit → Tape Γ)
  | 0, S => (KStmt.move (fun _ => some Dir.right)).apply S
  | (k + 1), S => retTape k ((KStmt.move (fun _ => some Dir.left)).apply S)

/-- **Return sweep.**  From `⟨ret, S⟩`, with the source non-blank at the head and
`k-1` cells leftward and blank at `-k`, `copyStr` sweeps left `k` times and steps
home, reaching `⟨done, retTape k S⟩`.  Moves only (content unchanged). -/
theorem copyStr_return (k : ℕ) : ∀ S : Unit ⊕ Unit → Tape Γ,
    (∀ i : ℕ, i < k → (S (Sum.inl ())).nth (-(i : ℤ)) ≠ default) →
    (S (Sum.inl ())).nth (-(k : ℤ)) = default →
    StateTransition.Reaches (kstep copyStr) ⟨CopyState.ret, S⟩
      ⟨CopyState.done, retTape k S⟩ := by
  induction k with
  | zero =>
    intro S _ hend
    have hb : (S (Sum.inl ())).1 = default := by
      have h := hend; simp only [Nat.cast_zero, neg_zero, Tape.nth_zero] at h; exact h
    exact Relation.ReflTransGen.head
      (Option.mem_def.mpr (copyStr_step_ret_blank hb)) Relation.ReflTransGen.refl
  | succ k ih =>
    intro S hblock hend
    have h0 : (S (Sum.inl ())).1 ≠ default := by
      have h := hblock 0 (Nat.succ_pos k)
      simp only [Nat.cast_zero, neg_zero] at h
      rwa [Tape.nth_zero] at h
    have hleft : ∀ i : ℤ, (((KStmt.move (fun _ => some Dir.left)).apply S)
        (Sum.inl ())).nth i = (S (Sum.inl ())).nth (i - 1) := by
      intro i
      show ((S (Sum.inl ())).move Dir.left).nth i = _
      exact Tape.move_left_nth _ i
    have hblock1 : ∀ i : ℕ, i < k → (((KStmt.move (fun _ => some Dir.left)).apply S)
        (Sum.inl ())).nth (-(i : ℤ)) ≠ default := by
      intro i hi
      rw [hleft, show (-(i : ℤ) - 1) = -((i + 1 : ℕ) : ℤ) by push_cast; ring]
      exact hblock (i + 1) (by omega)
    have hend1 : (((KStmt.move (fun _ => some Dir.left)).apply S)
        (Sum.inl ())).nth (-(k : ℤ)) = default := by
      rw [hleft, show (-(k : ℤ) - 1) = -((k + 1 : ℕ) : ℤ) by push_cast; ring]
      exact hend
    refine Relation.ReflTransGen.head
      (Option.mem_def.mpr (copyStr_step_ret_move h0)) ?_
    exact ih _ hblock1 hend1

/-! #### The full run -/

/-- After `n` forward macros the source content shifts: cell `m` of the result is
the original cell `n + m`. -/
theorem sweepTape_src_nth (n : ℕ) : ∀ (T : Unit ⊕ Unit → Tape Γ) (m : ℤ),
    (sweepTape n T (Sum.inl ())).nth m = (T (Sum.inl ())).nth (n + m) := by
  induction n with
  | zero => intro T m; simp [sweepTape]
  | succ n ih =>
    intro T m
    rw [sweepTape, ih, sweepOne_src_nth]
    congr 1
    push_cast; ring

/-- **Full `copyStr` run.**  On a blank-free contiguous block of length `n`
anchored at home (cells `0..n-1` non-blank, cells `n` and `-1` blank), `copyStr`
runs from `⟨copy, T⟩` to `⟨done, …⟩`: forward sweep to `ret`, then return sweep
home. -/
theorem copyStr_run (n : ℕ) (T : Unit ⊕ Unit → Tape Γ)
    (hblock : ∀ i : ℕ, i < n → (T (Sum.inl ())).nth i ≠ default)
    (hend : (T (Sum.inl ())).nth n = default)
    (hanchor : (T (Sum.inl ())).nth (-1) = default) :
    StateTransition.Reaches (kstep copyStr) ⟨CopyState.copy, T⟩
      ⟨CopyState.done,
        retTape n ((KStmt.move (fun _ => some Dir.left)).apply (sweepTape n T))⟩ := by
  refine (copyStr_forward_to_ret n T hblock hend).trans ?_
  have hnth : ∀ j : ℤ, (((KStmt.move (fun _ => some Dir.left)).apply (sweepTape n T))
      (Sum.inl ())).nth j = (T (Sum.inl ())).nth (n + (j - 1)) := by
    intro j
    show ((sweepTape n T (Sum.inl ())).move Dir.left).nth j = _
    rw [Tape.move_left_nth, sweepTape_src_nth]
  apply copyStr_return n
  · intro i hi
    rw [hnth, show ((n : ℤ) + (-(i : ℤ) - 1)) = ((n - 1 - i : ℕ) : ℤ) by omega]
    exact hblock (n - 1 - i) (by omega)
  · rw [hnth, show ((n : ℤ) + (-(n : ℤ) - 1)) = (-1 : ℤ) by ring]
    exact hanchor

/-! #### Content of the final tape (source bank) -/

/-- `n` move-rights are undone by `n` move-lefts. -/
theorem moveLR_cancel (n : ℕ) (x : Tape Γ) :
    (fun t : Tape Γ => t.move Dir.left)^[n] ((fun t : Tape Γ => t.move Dir.right)^[n] x) = x :=
  Function.LeftInverse.iterate (fun y => Tape.move_right_left y) n x

/-- The source bank after `n` forward macros is `n` move-rights of the original. -/
theorem sweepTape_src (n : ℕ) : ∀ T : Unit ⊕ Unit → Tape Γ,
    (sweepTape n T) (Sum.inl ()) = (fun t : Tape Γ => t.move Dir.right)^[n] (T (Sum.inl ())) := by
  induction n with
  | zero => intro T; rfl
  | succ n ih =>
    intro T
    rw [sweepTape, ih,
      show (((KStmt.move (fun _ => some Dir.right)).apply
          ((KStmt.write (fun _ => (T (Sum.inl ())).1)).apply T)) (Sum.inl ()))
          = (T (Sum.inl ())).move Dir.right from by
            show ((T (Sum.inl ())).write ((T (Sum.inl ())).1)).move Dir.right
                = (T (Sum.inl ())).move Dir.right
            rw [Tape.write_self],
      Function.iterate_succ_apply]

/-- The source bank after the return sweep is `k` move-lefts then one move-right. -/
theorem retTape_src (k : ℕ) : ∀ S : Unit ⊕ Unit → Tape Γ,
    (retTape k S) (Sum.inl ())
      = ((fun t : Tape Γ => t.move Dir.left)^[k] (S (Sum.inl ()))).move Dir.right := by
  induction k with
  | zero => intro S; rfl
  | succ k ih =>
    intro S
    rw [retTape, ih,
      show (((KStmt.move (fun _ => some Dir.left)).apply S) (Sum.inl ()))
          = (S (Sum.inl ())).move Dir.left from rfl,
      Function.iterate_succ_apply]

/-- **Source content invariant.**  `copyStr`'s full run leaves the source bank
unchanged (content and head): only no-op writes and cancelling moves touch it. -/
theorem copyStr_run_src (n : ℕ) (T : Unit ⊕ Unit → Tape Γ) :
    (retTape n ((KStmt.move (fun _ => some Dir.left)).apply (sweepTape n T))) (Sum.inl ())
      = T (Sum.inl ()) := by
  rw [retTape_src]
  show ((fun t : Tape Γ => t.move Dir.left)^[n]
      ((sweepTape n T (Sum.inl ())).move Dir.left)).move Dir.right = T (Sum.inl ())
  rw [sweepTape_src,
    show (((fun t : Tape Γ => t.move Dir.right)^[n] (T (Sum.inl ()))).move Dir.left)
        = (fun t : Tape Γ => t.move Dir.left)
            ((fun t : Tape Γ => t.move Dir.right)^[n] (T (Sum.inl ()))) from rfl,
    ← Function.iterate_succ_apply (fun t : Tape Γ => t.move Dir.left) n,
    Function.iterate_succ_apply' (fun t : Tape Γ => t.move Dir.left) n,
    moveLR_cancel]
  exact Tape.move_left_right _

/-! #### Content of the final tape (target bank) -/

/-- One macro on the target bank: writes the source head at the current cell, then
shifts (in `nth` terms, the write lands at `j + 1 = 0`). -/
theorem sweepOne_tgt_nth (T : Unit ⊕ Unit → Tape Γ) (j : ℤ) :
    (((KStmt.move (fun _ => some Dir.right)).apply
      ((KStmt.write (fun _ => (T (Sum.inl ())).1)).apply T)) (Sum.inr ())).nth j
      = if j + 1 = 0 then (T (Sum.inl ())).1 else (T (Sum.inr ())).nth (j + 1) := by
  show (((T (Sum.inr ())).write ((T (Sum.inl ())).1)).move Dir.right).nth j = _
  rw [Tape.move_right_nth, Tape.write_nth]

/-- **Target content after the forward sweep.**  Relative to the source head's
final position, cell `m` of the target holds the copied source cell when
`-n ≤ m < 0`, and the original target cell otherwise. -/
theorem sweepTape_tgt_nth (n : ℕ) : ∀ (T : Unit ⊕ Unit → Tape Γ) (m : ℤ),
    (sweepTape n T (Sum.inr ())).nth m
      = if (-(n : ℤ) ≤ m ∧ m < 0) then (T (Sum.inl ())).nth (n + m)
        else (T (Sum.inr ())).nth (n + m) := by
  induction n with
  | zero =>
    intro T m
    rw [if_neg (show ¬ (-((0 : ℕ) : ℤ) ≤ m ∧ m < 0) by omega)]
    simp [sweepTape]
  | succ n ih =>
    intro T m
    rw [sweepTape, ih]
    by_cases hc : -(n : ℤ) ≤ m ∧ m < 0
    · rw [if_pos hc, sweepOne_src_nth,
        if_pos (by omega : -((n + 1 : ℕ) : ℤ) ≤ m ∧ m < 0)]
      congr 1; push_cast; ring
    · rw [if_neg hc, sweepOne_tgt_nth]
      by_cases hz : (n : ℤ) + m + 1 = 0
      · rw [if_pos hz, if_pos (by omega : -((n + 1 : ℕ) : ℤ) ≤ m ∧ m < 0),
          show ((n + 1 : ℕ) : ℤ) + m = 0 by push_cast; omega, Tape.nth_zero]
      · rw [if_neg hz, if_neg (by omega : ¬ (-((n + 1 : ℕ) : ℤ) ≤ m ∧ m < 0))]
        congr 1; push_cast; ring

/-- `k` move-lefts shift `nth` by `-k`. -/
theorem iterateLeft_nth (n : ℕ) : ∀ (Y : Tape Γ) (m : ℤ),
    ((fun t : Tape Γ => t.move Dir.left)^[n] Y).nth m = Y.nth (m - n) := by
  induction n with
  | zero => intro Y m; simp
  | succ n ih =>
    intro Y m
    rw [Function.iterate_succ_apply']
    show (((fun t : Tape Γ => t.move Dir.left)^[n] Y).move Dir.left).nth m = _
    rw [Tape.move_left_nth, ih]
    congr 1; push_cast; ring

/-- The target bank after the return sweep is `k` move-lefts then a move-right. -/
theorem retTape_tgt (k : ℕ) : ∀ S : Unit ⊕ Unit → Tape Γ,
    (retTape k S) (Sum.inr ())
      = ((fun t : Tape Γ => t.move Dir.left)^[k] (S (Sum.inr ()))).move Dir.right := by
  induction k with
  | zero => intro S; rfl
  | succ k ih =>
    intro S
    rw [retTape, ih,
      show (((KStmt.move (fun _ => some Dir.left)).apply S) (Sum.inr ()))
          = (S (Sum.inr ())).move Dir.left from rfl,
      Function.iterate_succ_apply]

/-- **Target content of the full run.**  After `copyStr`, cell `m` of the target
holds the source cell `m` on the block `0 ≤ m < n`, and the original target cell
otherwise.  With a blank target input this is exactly the copy of the source
block. -/
theorem copyStr_run_tgt_nth (n : ℕ) (T : Unit ⊕ Unit → Tape Γ) (m : ℤ) :
    (retTape n ((KStmt.move (fun _ => some Dir.left)).apply (sweepTape n T))
        (Sum.inr ())).nth m
      = if (0 ≤ m ∧ m < (n : ℤ)) then (T (Sum.inl ())).nth m else (T (Sum.inr ())).nth m := by
  rw [retTape_tgt]
  show (((fun t : Tape Γ => t.move Dir.left)^[n]
      ((sweepTape n T (Sum.inr ())).move Dir.left)).move Dir.right).nth m = _
  rw [Tape.move_right_nth, iterateLeft_nth, Tape.move_left_nth,
    show ((m + 1) - (n : ℤ)) - 1 = m - (n : ℤ) from by ring, sweepTape_tgt_nth,
    show (n : ℤ) + (m - (n : ℤ)) = m from by ring]
  by_cases h : (0 : ℤ) ≤ m ∧ m < (n : ℤ)
  · rw [if_pos h, if_pos (show -(n : ℤ) ≤ m - n ∧ m - n < 0 by omega)]
  · rw [if_neg h, if_neg (show ¬ (-(n : ℤ) ≤ m - n ∧ m - n < 0) by omega)]

/-- The full-run output is a member of `copyStr`'s tape semantics (so it is *the*
value, by `Part.mem_unique`). -/
theorem copyStr_output_mem (n : ℕ) (X : Unit ⊕ Unit → Tape Γ)
    (hblock : ∀ i : ℕ, i < n → (X (Sum.inl ())).nth i ≠ default)
    (hend : (X (Sum.inl ())).nth n = default)
    (hanchor : (X (Sum.inl ())).nth (-1) = default) :
    (retTape n ((KStmt.move (fun _ => some Dir.left)).apply (sweepTape n X)))
      ∈ ktapeSem copyStr CopyState.copy X := by
  refine (Part.mem_map_iff _).mpr
    ⟨⟨CopyState.done,
        retTape n ((KStmt.move (fun _ => some Dir.left)).apply (sweepTape n X))⟩, ?_, rfl⟩
  exact StateTransition.mem_eval.mpr
    ⟨copyStr_run n X hblock hend hanchor, copyStr_step_done _⟩

/-! #### The reverse machine's run (mirrors `copyStr`, blanking the target) -/

/-- The tape after `n` reverse copy macros (blank the target each cell). -/
def sweepTapeRev : ℕ → (Unit ⊕ Unit → Tape Γ) → (Unit ⊕ Unit → Tape Γ)
  | 0, T => T
  | (n + 1), T => sweepTapeRev n ((KStmt.move (fun _ => some Dir.right)).apply
      ((KStmt.write (fun i => match i with
        | Sum.inl _ => (T (Sum.inl ())).1 | Sum.inr _ => default)).apply T))

/-- One reverse macro shifts the source `nth` by one (source write is a no-op). -/
theorem sweepOneRev_src_nth (T : Unit ⊕ Unit → Tape Γ) (i : ℤ) :
    (((KStmt.move (fun _ => some Dir.right)).apply
      ((KStmt.write (fun i => match i with
        | Sum.inl _ => (T (Sum.inl ())).1 | Sum.inr _ => default)).apply T)) (Sum.inl ())).nth i
      = (T (Sum.inl ())).nth (i + 1) := by
  show (((T (Sum.inl ())).write ((T (Sum.inl ())).1)).move Dir.right).nth i
      = (T (Sum.inl ())).nth (i + 1)
  rw [Tape.write_self]
  exact Tape.move_right_nth _ i

theorem copyStrRev_forward_sweep (n : ℕ) : ∀ (T : Unit ⊕ Unit → Tape Γ),
    (∀ i : ℕ, i < n → (T (Sum.inl ())).nth i ≠ default) →
    StateTransition.Reaches (kstep copyStrRev) ⟨CopyState.copy, T⟩
      ⟨CopyState.copy, sweepTapeRev n T⟩ := by
  induction n with
  | zero => intro T _; exact Relation.ReflTransGen.refl
  | succ n ih =>
    intro T hblock
    have h0 : (T (Sum.inl ())).1 ≠ default := by
      have h := hblock 0 (Nat.succ_pos n); simpa using h
    have hblock1 : ∀ i : ℕ, i < n → (((KStmt.move (fun _ => some Dir.right)).apply
        ((KStmt.write (fun i => match i with
          | Sum.inl _ => (T (Sum.inl ())).1 | Sum.inr _ => default)).apply T))
        (Sum.inl ())).nth i ≠ default := by
      intro i hi
      rw [sweepOneRev_src_nth, show ((i : ℤ) + 1) = ((i + 1 : ℕ) : ℤ) by push_cast; ring]
      exact hblock (i + 1) (by omega)
    exact (copyStrRev_macro h0).trans (ih _ hblock1)

theorem sweepTapeRev_src_head (n : ℕ) : ∀ T : Unit ⊕ Unit → Tape Γ,
    (sweepTapeRev n T (Sum.inl ())).1 = (T (Sum.inl ())).nth n := by
  induction n with
  | zero => intro T; simp [sweepTapeRev, Tape.nth_zero]
  | succ n ih =>
    intro T
    rw [sweepTapeRev, ih, sweepOneRev_src_nth,
      show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring]

theorem copyStrRev_forward_to_ret (n : ℕ) (T : Unit ⊕ Unit → Tape Γ)
    (hblock : ∀ i : ℕ, i < n → (T (Sum.inl ())).nth i ≠ default)
    (hend : (T (Sum.inl ())).nth n = default) :
    StateTransition.Reaches (kstep copyStrRev) ⟨CopyState.copy, T⟩
      ⟨CopyState.ret, (KStmt.move (fun _ => some Dir.left)).apply (sweepTapeRev n T)⟩ := by
  refine (copyStrRev_forward_sweep n T hblock).trans ?_
  have hb : (sweepTapeRev n T (Sum.inl ())).1 = default := by
    rw [sweepTapeRev_src_head]; exact hend
  exact Relation.ReflTransGen.head
    (Option.mem_def.mpr (copyStrRev_step_copy_blank hb)) Relation.ReflTransGen.refl

theorem sweepTapeRev_src_nth (n : ℕ) : ∀ (T : Unit ⊕ Unit → Tape Γ) (m : ℤ),
    (sweepTapeRev n T (Sum.inl ())).nth m = (T (Sum.inl ())).nth (n + m) := by
  induction n with
  | zero => intro T m; simp [sweepTapeRev]
  | succ n ih =>
    intro T m
    rw [sweepTapeRev, ih, sweepOneRev_src_nth]
    congr 1; push_cast; ring

theorem copyStrRev_return (k : ℕ) : ∀ S : Unit ⊕ Unit → Tape Γ,
    (∀ i : ℕ, i < k → (S (Sum.inl ())).nth (-(i : ℤ)) ≠ default) →
    (S (Sum.inl ())).nth (-(k : ℤ)) = default →
    StateTransition.Reaches (kstep copyStrRev) ⟨CopyState.ret, S⟩
      ⟨CopyState.done, retTape k S⟩ := by
  induction k with
  | zero =>
    intro S _ hend
    have hb : (S (Sum.inl ())).1 = default := by
      have h := hend; simp only [Nat.cast_zero, neg_zero, Tape.nth_zero] at h; exact h
    exact Relation.ReflTransGen.head
      (Option.mem_def.mpr (copyStrRev_step_ret_blank hb)) Relation.ReflTransGen.refl
  | succ k ih =>
    intro S hblock hend
    have h0 : (S (Sum.inl ())).1 ≠ default := by
      have h := hblock 0 (Nat.succ_pos k)
      simp only [Nat.cast_zero, neg_zero] at h
      rwa [Tape.nth_zero] at h
    have hleft : ∀ i : ℤ, (((KStmt.move (fun _ => some Dir.left)).apply S)
        (Sum.inl ())).nth i = (S (Sum.inl ())).nth (i - 1) := by
      intro i
      show ((S (Sum.inl ())).move Dir.left).nth i = _
      exact Tape.move_left_nth _ i
    have hblock1 : ∀ i : ℕ, i < k → (((KStmt.move (fun _ => some Dir.left)).apply S)
        (Sum.inl ())).nth (-(i : ℤ)) ≠ default := by
      intro i hi
      rw [hleft, show (-(i : ℤ) - 1) = -((i + 1 : ℕ) : ℤ) by push_cast; ring]
      exact hblock (i + 1) (by omega)
    have hend1 : (((KStmt.move (fun _ => some Dir.left)).apply S)
        (Sum.inl ())).nth (-(k : ℤ)) = default := by
      rw [hleft, show (-(k : ℤ) - 1) = -((k + 1 : ℕ) : ℤ) by push_cast; ring]
      exact hend
    refine Relation.ReflTransGen.head
      (Option.mem_def.mpr (copyStrRev_step_ret_move h0)) ?_
    exact ih _ hblock1 hend1

/-- **Full `copyStrRev` run** (same domain as `copyStr`). -/
theorem copyStrRev_run (n : ℕ) (T : Unit ⊕ Unit → Tape Γ)
    (hblock : ∀ i : ℕ, i < n → (T (Sum.inl ())).nth i ≠ default)
    (hend : (T (Sum.inl ())).nth n = default)
    (hanchor : (T (Sum.inl ())).nth (-1) = default) :
    StateTransition.Reaches (kstep copyStrRev) ⟨CopyState.copy, T⟩
      ⟨CopyState.done,
        retTape n ((KStmt.move (fun _ => some Dir.left)).apply (sweepTapeRev n T))⟩ := by
  refine (copyStrRev_forward_to_ret n T hblock hend).trans ?_
  have hnth : ∀ j : ℤ, (((KStmt.move (fun _ => some Dir.left)).apply (sweepTapeRev n T))
      (Sum.inl ())).nth j = (T (Sum.inl ())).nth (n + (j - 1)) := by
    intro j
    show ((sweepTapeRev n T (Sum.inl ())).move Dir.left).nth j = _
    rw [Tape.move_left_nth, sweepTapeRev_src_nth]
  apply copyStrRev_return n
  · intro i hi
    rw [hnth, show ((n : ℤ) + (-(i : ℤ) - 1)) = ((n - 1 - i : ℕ) : ℤ) by omega]
    exact hblock (n - 1 - i) (by omega)
  · rw [hnth, show ((n : ℤ) + (-(n : ℤ) - 1)) = (-1 : ℤ) by ring]
    exact hanchor

/-! #### Content of the reverse run -/

theorem sweepTapeRev_src (n : ℕ) : ∀ T : Unit ⊕ Unit → Tape Γ,
    (sweepTapeRev n T) (Sum.inl ()) = (fun t : Tape Γ => t.move Dir.right)^[n] (T (Sum.inl ())) := by
  induction n with
  | zero => intro T; rfl
  | succ n ih =>
    intro T
    rw [sweepTapeRev, ih,
      show (((KStmt.move (fun _ => some Dir.right)).apply
          ((KStmt.write (fun i => match i with
            | Sum.inl _ => (T (Sum.inl ())).1 | Sum.inr _ => default)).apply T)) (Sum.inl ()))
          = (T (Sum.inl ())).move Dir.right from by
            show ((T (Sum.inl ())).write ((T (Sum.inl ())).1)).move Dir.right
                = (T (Sum.inl ())).move Dir.right
            rw [Tape.write_self],
      Function.iterate_succ_apply]

theorem copyStrRev_run_src (n : ℕ) (T : Unit ⊕ Unit → Tape Γ) :
    (retTape n ((KStmt.move (fun _ => some Dir.left)).apply (sweepTapeRev n T))) (Sum.inl ())
      = T (Sum.inl ()) := by
  rw [retTape_src]
  show ((fun t : Tape Γ => t.move Dir.left)^[n]
      ((sweepTapeRev n T (Sum.inl ())).move Dir.left)).move Dir.right = T (Sum.inl ())
  rw [sweepTapeRev_src,
    show (((fun t : Tape Γ => t.move Dir.right)^[n] (T (Sum.inl ()))).move Dir.left)
        = (fun t : Tape Γ => t.move Dir.left)
            ((fun t : Tape Γ => t.move Dir.right)^[n] (T (Sum.inl ()))) from rfl,
    ← Function.iterate_succ_apply (fun t : Tape Γ => t.move Dir.left) n,
    Function.iterate_succ_apply' (fun t : Tape Γ => t.move Dir.left) n,
    moveLR_cancel]
  exact Tape.move_left_right _

theorem sweepOneRev_tgt_nth (T : Unit ⊕ Unit → Tape Γ) (j : ℤ) :
    (((KStmt.move (fun _ => some Dir.right)).apply
      ((KStmt.write (fun i => match i with
        | Sum.inl _ => (T (Sum.inl ())).1 | Sum.inr _ => default)).apply T)) (Sum.inr ())).nth j
      = if j + 1 = 0 then default else (T (Sum.inr ())).nth (j + 1) := by
  show (((T (Sum.inr ())).write default).move Dir.right).nth j = _
  rw [Tape.move_right_nth, Tape.write_nth]

theorem sweepTapeRev_tgt_nth (n : ℕ) : ∀ (T : Unit ⊕ Unit → Tape Γ) (m : ℤ),
    (sweepTapeRev n T (Sum.inr ())).nth m
      = if (-(n : ℤ) ≤ m ∧ m < 0) then default else (T (Sum.inr ())).nth (n + m) := by
  induction n with
  | zero =>
    intro T m
    rw [if_neg (show ¬ (-((0 : ℕ) : ℤ) ≤ m ∧ m < 0) by omega)]
    simp [sweepTapeRev]
  | succ n ih =>
    intro T m
    rw [sweepTapeRev, ih]
    by_cases hc : -(n : ℤ) ≤ m ∧ m < 0
    · rw [if_pos hc, if_pos (by omega : -((n + 1 : ℕ) : ℤ) ≤ m ∧ m < 0)]
    · rw [if_neg hc, sweepOneRev_tgt_nth]
      by_cases hz : (n : ℤ) + m + 1 = 0
      · rw [if_pos hz, if_pos (by omega : -((n + 1 : ℕ) : ℤ) ≤ m ∧ m < 0)]
      · rw [if_neg hz, if_neg (by omega : ¬ (-((n + 1 : ℕ) : ℤ) ≤ m ∧ m < 0))]
        congr 1; push_cast; ring

theorem copyStrRev_run_tgt_nth (n : ℕ) (T : Unit ⊕ Unit → Tape Γ) (m : ℤ) :
    (retTape n ((KStmt.move (fun _ => some Dir.left)).apply (sweepTapeRev n T))
        (Sum.inr ())).nth m
      = if (0 ≤ m ∧ m < (n : ℤ)) then default else (T (Sum.inr ())).nth m := by
  rw [retTape_tgt]
  show (((fun t : Tape Γ => t.move Dir.left)^[n]
      ((sweepTapeRev n T (Sum.inr ())).move Dir.left)).move Dir.right).nth m = _
  rw [Tape.move_right_nth, iterateLeft_nth, Tape.move_left_nth,
    show ((m + 1) - (n : ℤ)) - 1 = m - (n : ℤ) from by ring, sweepTapeRev_tgt_nth,
    show (n : ℤ) + (m - (n : ℤ)) = m from by ring]
  by_cases h : (0 : ℤ) ≤ m ∧ m < (n : ℤ)
  · rw [if_pos h, if_pos (show -(n : ℤ) ≤ m - n ∧ m - n < 0 by omega)]
  · rw [if_neg h, if_neg (show ¬ (-(n : ℤ) ≤ m - n ∧ m - n < 0) by omega)]

/-! #### Semantic inverse -/

/-- Input domain: source anchored at home (blank at `-1`), a blank-free block from
`0` (length `n`), and a blank target. -/
def CopyDomIn (X : Unit ⊕ Unit → Tape Γ) : Prop :=
  (X (Sum.inl ())).nth (-1) = default ∧
  (∀ m : ℤ, (X (Sum.inr ())).nth m = default) ∧
  ∃ n : ℕ, (∀ i : ℕ, i < n → (X (Sum.inl ())).nth i ≠ default) ∧
    (X (Sum.inl ())).nth n = default

/-- Output domain: the image of `copyStr` from `CopyDomIn`. -/
def CopyDomOut (Y : Unit ⊕ Unit → Tape Γ) : Prop :=
  ∃ X, CopyDomIn X ∧ Y ∈ ktapeSem copyStr CopyState.copy X

/-- Forward leg: on a `CopyDomIn` input, `copyStrRev` undoes `copyStr`. -/
theorem copyStr_semInverse_fwd (X Y : Unit ⊕ Unit → Tape Γ)
    (hX : CopyDomIn X) (hXY : Y ∈ ktapeSem copyStr CopyState.copy X) :
    X ∈ ktapeSem copyStrRev CopyState.copy Y := by
  obtain ⟨hanchor, htgt, n, hblock, hend⟩ := hX
  have hYeq : Y = retTape n ((KStmt.move (fun _ => some Dir.left)).apply (sweepTape n X)) :=
    Part.mem_unique hXY (copyStr_output_mem n X hblock hend hanchor)
  rw [hYeq]
  have hsrc : ∀ i : ℤ,
      (retTape n ((KStmt.move (fun _ => some Dir.left)).apply (sweepTape n X))
        (Sum.inl ())).nth i = (X (Sum.inl ())).nth i := fun i => by rw [copyStr_run_src]
  have hb : ∀ i : ℕ, i < n →
      (retTape n ((KStmt.move (fun _ => some Dir.left)).apply (sweepTape n X))
        (Sum.inl ())).nth i ≠ default := fun i hi => by rw [hsrc]; exact hblock i hi
  have he : (retTape n ((KStmt.move (fun _ => some Dir.left)).apply (sweepTape n X))
      (Sum.inl ())).nth n = default := by rw [hsrc]; exact hend
  have ha : (retTape n ((KStmt.move (fun _ => some Dir.left)).apply (sweepTape n X))
      (Sum.inl ())).nth (-1) = default := by rw [hsrc]; exact hanchor
  have hrun := copyStrRev_run n _ hb he ha
  have hXeq : retTape n ((KStmt.move (fun _ => some Dir.left)).apply
      (sweepTapeRev n (retTape n ((KStmt.move (fun _ => some Dir.left)).apply
        (sweepTape n X))))) = X := by
    funext b
    cases b with
    | inl u => cases u; rw [copyStrRev_run_src, copyStr_run_src]
    | inr u =>
      cases u
      apply tape_ext_nth
      intro m
      rw [copyStrRev_run_tgt_nth, copyStr_run_tgt_nth]
      by_cases hm : (0 : ℤ) ≤ m ∧ m < (n : ℤ)
      · rw [if_pos hm]; exact (htgt m).symm
      · rw [if_neg hm, if_neg hm]
  exact (Part.mem_map_iff _).mpr
    ⟨⟨CopyState.done, _⟩,
      StateTransition.mem_eval.mpr ⟨hrun, copyStrRev_step_done _⟩, hXeq⟩

/-- **The full-string copy preserves the source bank.**  On a `CopyDomIn` input
the run halts with the source restored, so any output agrees with the input on the
source bank.  (Domain-gated: unlike the single-write `copyM`, the traversal copy
only halts on the blank-free-block domain.) -/
theorem copyStr_preserves_src (X V : Unit ⊕ Unit → Tape Γ)
    (hX : CopyDomIn X) (hV : V ∈ ktapeSem copyStr CopyState.copy X) :
    V (Sum.inl ()) = X (Sum.inl ()) := by
  obtain ⟨hanchor, _htgt, n, hblock, hend⟩ := hX
  have hVeq : V = retTape n ((KStmt.move (fun _ => some Dir.left)).apply (sweepTape n X)) :=
    Part.mem_unique hV (copyStr_output_mem n X hblock hend hanchor)
  rw [hVeq]; exact copyStr_run_src n X

/-- **A-lean-3: the full-string copy is semantically reversible.**  `copyStrRev`
is a `SemInverse` of `copyStr` on the blank-free-block / blank-target domain. -/
theorem copyStr_semInverse :
    SemInverse (Γ := Γ) (ι := Unit ⊕ Unit) copyStr copyStrRev
      CopyState.copy CopyState.copy CopyDomIn CopyDomOut where
  fwd := copyStr_semInverse_fwd
  bwd := by
    intro X Y hY hXY
    obtain ⟨X₀, hX₀dom, hYX₀⟩ := hY
    have h1 := copyStr_semInverse_fwd X₀ Y hX₀dom hYX₀
    rw [Part.mem_unique hXY h1]
    exact hYX₀

/-! #### Wrapper-layout copy (transport into the Bennett bank layout)

`copyStr` lives on the 2-bank index `Unit ⊕ Unit` (source, target).  The Bennett
F;C;U wrapper runs its copy leg on `(ι ⊕ τ) ⊕ ι` with `ι = Unit`, `τ = Fin 1`,
i.e. `(Unit ⊕ Fin 1) ⊕ Unit`: a left work bank, a frozen `Fin 1` ancilla, and the
right output bank.  `bankEquiv` is the bijection that drops `copyStr`'s two banks
into that layout (source → left work, target → right output, frozen ancilla
unused), and `copyStrW` / `copyStrWrev` are `copyStr` / `copyStrRev` transported
along it via `renameBank ∘ liftL`. -/

/-- Bank-index bijection placing `copyStr`'s `(source, target)` banks into the
Bennett copy-leg layout `(Unit ⊕ Fin 1) ⊕ Unit`. -/
def bankEquiv : ((Unit ⊕ Unit) ⊕ Fin 1) ≃ ((Unit ⊕ Fin 1) ⊕ Unit) where
  toFun := fun
    | Sum.inl (Sum.inl ()) => Sum.inl (Sum.inl ())
    | Sum.inl (Sum.inr ()) => Sum.inr ()
    | Sum.inr c => Sum.inl (Sum.inr c)
  invFun := fun
    | Sum.inl (Sum.inl ()) => Sum.inl (Sum.inl ())
    | Sum.inl (Sum.inr c) => Sum.inr c
    | Sum.inr () => Sum.inl (Sum.inr ())
  left_inv := by rintro ((⟨⟩ | ⟨⟩) | c) <;> rfl
  right_inv := by rintro ((⟨⟩ | c) | ⟨⟩) <;> rfl

/-- `copyStr` transported into the Bennett copy-leg bank layout. -/
def copyStrW : KMachine Γ CopyState ((Unit ⊕ Fin 1) ⊕ Unit) :=
  renameBank bankEquiv (liftL copyStr (κ := Fin 1))

/-- `copyStrRev` transported into the Bennett copy-leg bank layout. -/
def copyStrWrev : KMachine Γ CopyState ((Unit ⊕ Fin 1) ⊕ Unit) :=
  renameBank bankEquiv (liftL copyStrRev (κ := Fin 1))

/-- **The wrapper-layout full-string copy is semantically reversible.**
`copyStr_semInverse` transported through `liftL` (a frozen `Fin 1` ancilla) and
then `renameBank bankEquiv` into the `(Unit ⊕ Fin 1) ⊕ Unit` layout. -/
theorem copyStrW_semInverse :
    SemInverse (Γ := Γ) copyStrW copyStrWrev CopyState.copy CopyState.copy
      (fun T' => CopyDomIn (fun i => T' (bankEquiv (Sum.inl i))))
      (fun T' => CopyDomOut (fun i => T' (bankEquiv (Sum.inl i)))) :=
  (copyStr_semInverse.liftL (κ := Fin 1)).renameBank bankEquiv

/-- **The wrapper-layout copy preserves the `Sum.inl` (work ⊕ ancilla) banks.**
The source bank is restored by `copyStr_preserves_src`; the frozen `Fin 1` ancilla
is preserved by `liftL`.  Mirrors `copyWA_preserves_left` and discharges the
`hCompatO` hand-over of the F;C;U wrapper (work⊕history block survives the copy). -/
theorem copyStrW_preserves_left (Y V : (Unit ⊕ Fin 1) ⊕ Unit → Tape Γ)
    (hX : CopyDomIn (fun i => Y (bankEquiv (Sum.inl i))))
    (hV : V ∈ ktapeSem copyStrW CopyState.copy Y) :
    ∀ x, V (Sum.inl x) = Y (Sum.inl x) := by
  rw [copyStrW, ktapeSem_renameBank, Part.mem_map_iff] at hV
  obtain ⟨UL, hUL, rfl⟩ := hV
  obtain ⟨hfrozen, hleft⟩ := ktapeSem_liftL_mem copyStr CopyState.copy hUL
  intro x
  cases x with
  | inl u =>
    cases u
    show UL (bankEquiv.symm (Sum.inl (Sum.inl ()))) = Y (Sum.inl (Sum.inl ()))
    exact copyStr_preserves_src _ _ hX hleft
  | inr c =>
    show UL (bankEquiv.symm (Sum.inl (Sum.inr c))) = Y (Sum.inl (Sum.inr c))
    exact congrFun hfrozen c

end CopyStr

end PeriodicTM
