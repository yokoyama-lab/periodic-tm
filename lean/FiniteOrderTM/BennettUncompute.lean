/-
# The Bennett uncompute machine `phaseU2` (R1 Stage 1c)

`phaseF2` (BennettReversible.lean) is the forward descriptor-encoding Bennett
simulator.  It is semantically reversible (`phaseF2_kstep_inj_on_wf`,
`phaseF2_reachesN_inj_on_wf`) and injective (`phaseF2_ktapeSem_inj`), but it is
NOT `KReversible` (`phaseF2_not_backdet`).  The R2 bridge (`SemReversible.lean`)
reduced the unconditional symmetrisation to exhibiting an inverse *machine* `R'`
with `SemInverse (phaseF2 M₀) R' (.A1 q₀) ? Dom`.

This file defines that machine, `phaseU2`, validated first in the Python
prototype `proto/bennett_uncompute.py`: it runs `phaseF2`'s 4-state cycle
backwards, seeking left along the history, reading each descriptor, undoing the
recorded step, and erasing the descriptor, until the history head returns past
position 0.

State correspondence (forward `phaseF2` step  vs  reverse `phaseU2` step):

    forward   A1 q  →  S q a  →  S2 q a  →  C q'  →  A1 q'
    reverse   RStart → RB → RC q a → RD q a → RStart   (and RFin to halt)

* `RStart` : move the history head one step left, then inspect (→ `RB`).
* `RB`     : read the history cell.  A descriptor `step q a` → erase it and go
             to `RC q a`; a blank → we have passed position 0, move right and
             halt (→ `RFin`).
* `RC q a` : undo the forward `S` work-op (move `revMap d` / perm `π⁻¹` / no-op),
             recomputed from `M₀ q a` (→ `RD q a`).
* `RD q a` : undo the forward `A1` work write (restore the old heads `a` for a
             write rule; identity for move/perm) (→ `RStart`).
* `RFin`   : halt.

The `RB` rule reads the tape, so `phaseU2` is deliberately not head-uniform /
`KReversible` -- it is a *semantic* inverse, which is all the bridge needs.

STATUS.  The definition and the cheap structural lemmas are `sorry`-free.  The
SemInverse proof (`phaseF2_semInverse`) is the Stage-1c frontier and is a
documented `sorry`: the forward leg is a trace correspondence between the two
machines' runs (reuse `phaseF2_reachesN_inj_on_wf` / `phaseF2_backdet_on_wf`),
the backward leg holds on the reachable-output domain.
-/
import FiniteOrderTM.BennettReversible
import FiniteOrderTM.BennettWF
import FiniteOrderTM.SemReversible
import FiniteOrderTM.Unconditional

namespace PeriodicTM

open Turing

variable {Γ : Type*} [Inhabited Γ] [DecidableEq Γ]
variable {Λ : Type*}
variable {ι : Type*}

/-- State of the uncompute (reverse) machine; mirrors `phaseF2`'s
`C/S2/S/A1` cycle backwards (see the module doc). -/
inductive UncompState (Γ : Type*) (Λ : Type*) (ι : Type*)
  | RStart                  : UncompState Γ Λ ι
  | RB                      : UncompState Γ Λ ι
  | RC (q : Λ) (a : ι → Γ)  : UncompState Γ Λ ι
  | RD (q : Λ) (a : ι → Γ)  : UncompState Γ Λ ι
  | RFin                    : UncompState Γ Λ ι

/-- The Bennett uncompute machine: runs `phaseF2` backwards. -/
noncomputable def phaseU2 (M₀ : KMachine Γ Λ ι) :
    KMachine (BennettAlph2 Γ Λ ι) (UncompState Γ Λ ι) (ι ⊕ Fin 1) :=
  fun s b =>
  match s with
  | .RStart =>
    -- move the history head one step left
    some (.RB, KStmt.move (fun i => match i with
      | Sum.inl _ => none
      | Sum.inr _ => some Dir.left))
  | .RB =>
    match b (Sum.inr (0 : Fin 1)) with
    | Sum.inr (HistEntry2.step q a) =>
      -- erase the descriptor (write the work blank on the history cell), keep work
      some (.RC q a, KStmt.write (fun i => match i with
        | Sum.inl j => b (Sum.inl j)
        | Sum.inr _ => Sum.inl default))
    | Sum.inl _ =>
      -- blank: passed history position 0 -> reposition right and finish
      some (.RFin, KStmt.move (fun i => match i with
        | Sum.inl _ => none
        | Sum.inr _ => some Dir.right))
  | .RC q a =>
    -- undo the forward S work-op, recomputed from M₀ q a
    match M₀ q a with
    | none => none
    | some (_, KStmt.write _) =>
      -- forward S was a no-op move
      some (.RD q a, KStmt.move (fun _ => none))
    | some (_, KStmt.move d) =>
      some (.RD q a, KStmt.move (fun i => match i with
        | Sum.inl j => (d j).map dirRev
        | Sum.inr _ => none))
    | some (_, KStmt.perm π) =>
      some (.RD q a, KStmt.perm (Equiv.sumCongr π⁻¹ (Equiv.refl _)))
  | .RD q a =>
    -- undo the forward A1 work write
    match M₀ q a with
    | none => none
    | some (_, KStmt.write _) =>
      -- restore the old work heads a (history cell stays put)
      some (.RStart, KStmt.write (fun i => match i with
        | Sum.inl j => Sum.inl (a j)
        | Sum.inr k => b (Sum.inr k)))
    | some (_, KStmt.move _) =>
      some (.RStart, KStmt.write b)  -- forward A1 was an identity write
    | some (_, KStmt.perm _) =>
      some (.RStart, KStmt.write b)
  | .RFin => none

/-! ### Cheap structural lemmas (no `sorry`) -/

/-- `RStart` always steps (the seek-left is unconditional). -/
theorem phaseU2_RStart_isSome (M₀ : KMachine Γ Λ ι) (b : ι ⊕ Fin 1 → BennettAlph2 Γ Λ ι) :
    (phaseU2 M₀ .RStart b).isSome := by
  simp [phaseU2]

/-- `RB` always steps (either erase-a-descriptor or reposition-and-finish). -/
theorem phaseU2_RB_isSome (M₀ : KMachine Γ Λ ι) (b : ι ⊕ Fin 1 → BennettAlph2 Γ Λ ι) :
    (phaseU2 M₀ .RB b).isSome := by
  simp only [phaseU2]
  rcases b (Sum.inr 0) with x | he
  · simp
  · rcases he with ⟨q, a⟩; simp

/-- `phaseU2` halts only at `RFin`, or at `RC/RD` whose recomputation `M₀ q a`
is `none` (which never happens on reachable configs, where the descriptor came
from a real forward step). -/
theorem phaseU2_halt (M₀ : KMachine Γ Λ ι) {s : UncompState Γ Λ ι}
    {b : ι ⊕ Fin 1 → BennettAlph2 Γ Λ ι} (h : phaseU2 M₀ s b = none) :
    s = .RFin ∨ (∃ q a, s = .RC q a ∧ M₀ q a = none)
            ∨ (∃ q a, s = .RD q a ∧ M₀ q a = none) := by
  cases s with
  | RStart => simp [phaseU2] at h
  | RB =>
    exfalso
    have := phaseU2_RB_isSome M₀ b
    rw [h] at this; simp at this
  | RC q a =>
    refine Or.inr (Or.inl ⟨q, a, rfl, ?_⟩)
    simp only [phaseU2] at h
    rcases hm : M₀ q a with _ | ⟨q', st⟩
    · rfl
    · rw [hm] at h; cases st <;> simp at h
  | RD q a =>
    refine Or.inr (Or.inr ⟨q, a, rfl, ?_⟩)
    simp only [phaseU2] at h
    rcases hm : M₀ q a with _ | ⟨q', st⟩
    · rfl
    · rw [hm] at h; cases st <;> simp at h
  | RFin => exact Or.inl rfl

/-! ### Terminal step (no `sorry`)

The end of a reverse run: once the history head has passed position 0 (its
cell, one step left, is blank), `phaseU2` does `RStart → RB → RFin` and halts
with all tapes unchanged -- the history head moves left then right
(`tape_move_dirRev`) and the work banks are never touched.  This is the base
case that the trace leg lands on after undoing every macro-step. -/
theorem phaseU2_terminal (M₀ : KMachine Γ Λ ι)
    (T : ι ⊕ Fin 1 → Tape (BennettAlph2 Γ Λ ι))
    (hblank : ((T (Sum.inr 0)).move Dir.left).1 = (Sum.inl default : BennettAlph2 Γ Λ ι)) :
    T ∈ ktapeSem (phaseU2 M₀) UncompState.RStart T := by
  -- the three configs of the terminal run
  set c0 : KCfg (BennettAlph2 Γ Λ ι) (UncompState Γ Λ ι) (ι ⊕ Fin 1) :=
    ⟨.RStart, T⟩ with hc0
  -- step 1: RStart moves the history head left
  set T1 : ι ⊕ Fin 1 → Tape (BennettAlph2 Γ Λ ι) :=
    fun i => match i with | Sum.inl j => T (Sum.inl j) | Sum.inr k => (T (Sum.inr k)).move Dir.left
    with hT1
  have htapes0 : (KStmt.move (fun i : ι ⊕ Fin 1 => match i with
      | Sum.inl _ => none | Sum.inr _ => some Dir.left)).apply T = T1 := by
    funext i; cases i <;> simp [KStmt.apply, hT1]
  have hstep0 : kstep (phaseU2 M₀) c0 = some ⟨.RB, T1⟩ := by
    simp only [kstep, phaseU2, hc0, htapes0, Option.map_some]
  -- step 2: RB reads blank (history head) -> moves right, to RFin
  have hread : headsV T1 (Sum.inr (0 : Fin 1)) = (Sum.inl default : BennettAlph2 Γ Λ ι) := by
    simp only [headsV, hT1]; exact hblank
  have htapes1 : (KStmt.move (fun i : ι ⊕ Fin 1 => match i with
      | Sum.inl _ => none | Sum.inr _ => some Dir.right)).apply T1 = T := by
    funext i
    cases i with
    | inl j => simp [KStmt.apply, hT1]
    | inr k =>
      simp only [KStmt.apply, hT1]
      exact tape_move_dirRev (T (Sum.inr k)) Dir.left
  have hstep1 : kstep (phaseU2 M₀) ⟨.RB, T1⟩ = some ⟨.RFin, T⟩ := by
    simp only [kstep, phaseU2, hread, htapes1, Option.map_some]
  -- RFin halts
  have hhalt : kstep (phaseU2 M₀) ⟨.RFin, T⟩ = none := by simp [kstep, phaseU2]
  -- assemble the eval membership
  refine (Part.mem_map_iff _).mpr ⟨⟨.RFin, T⟩, ?_, rfl⟩
  refine StateTransition.mem_eval.mpr ⟨?_, hhalt⟩
  refine Relation.ReflTransGen.head (b := ⟨.RB, T1⟩) ?_
    (Relation.ReflTransGen.head (b := ⟨.RFin, T⟩) ?_ Relation.ReflTransGen.refl)
  · exact Option.mem_def.mpr hstep0
  · exact Option.mem_def.mpr hstep1

/-- Forward `C → A1` single step: `phaseF2` advances the history head right and
keeps the work banks.  A clean building block for the forward macro-step (it has
no case split and no descriptor logic). -/
theorem phaseF2_step_C (M₀ : KMachine Γ Λ ι) (q' : Λ)
    (T : ι ⊕ Fin 1 → Tape (BennettAlph2 Γ Λ ι)) :
    kstep (phaseF2 M₀) ⟨.C q', T⟩ = some ⟨.A1 q',
      fun i => match i with
        | Sum.inl j => T (Sum.inl j)
        | Sum.inr k => (T (Sum.inr k)).move Dir.right⟩ := by
  simp only [kstep, phaseF2, Option.map_some]
  refine congrArg some ?_
  refine congr (congrArg KCfg.mk rfl) ?_
  funext i; cases i <;> simp [KStmt.apply]

/-- Forward `S → S2`, write rule: the work-op is a no-op move; tapes unchanged. -/
theorem phaseF2_S_write (M₀ : KMachine Γ Λ ι) (q : Λ) (a : ι → Γ)
    (T : ι ⊕ Fin 1 → Tape (BennettAlph2 Γ Λ ι)) {q' : Λ} {b' : ι → Γ}
    (hr : M₀ q a = some (q', KStmt.write b')) :
    kstep (phaseF2 M₀) ⟨.S q a, T⟩ = some ⟨.S2 q a, T⟩ := by
  have hid : (KStmt.move (fun _ : ι ⊕ Fin 1 => none)).apply T = T := by
    funext i; simp [KStmt.apply]
  simp only [kstep, phaseF2, hr, Option.map_some]
  exact congrArg some (congr (congrArg KCfg.mk rfl) hid)

/-- Forward `S → S2`, move rule: move the work banks by `d` (history stays). -/
theorem phaseF2_S_move (M₀ : KMachine Γ Λ ι) (q : Λ) (a : ι → Γ)
    (T : ι ⊕ Fin 1 → Tape (BennettAlph2 Γ Λ ι)) {q' : Λ} {d : ι → Option Dir}
    (hr : M₀ q a = some (q', KStmt.move d)) :
    kstep (phaseF2 M₀) ⟨.S q a, T⟩ = some ⟨.S2 q a,
      (KStmt.move (fun i => match i with
        | Sum.inl j => d j | Sum.inr _ => none)).apply T⟩ := by
  simp only [kstep, phaseF2, hr, Option.map_some]
  refine congrArg some ?_
  refine congr (congrArg KCfg.mk rfl) ?_
  funext i; cases i <;> simp [KStmt.apply]

/-- Forward `S → S2`, perm rule: permute the work banks by `π`. -/
theorem phaseF2_S_perm (M₀ : KMachine Γ Λ ι) (q : Λ) (a : ι → Γ)
    (T : ι ⊕ Fin 1 → Tape (BennettAlph2 Γ Λ ι)) {q' : Λ} {π : Equiv.Perm ι}
    (hr : M₀ q a = some (q', KStmt.perm π)) :
    kstep (phaseF2 M₀) ⟨.S q a, T⟩ = some ⟨.S2 q a,
      (KStmt.perm (Equiv.sumCongr π (Equiv.refl (Fin 1)))).apply T⟩ := by
  simp only [kstep, phaseF2, hr, Option.map_some]

/-- Forward `S2 → C` single step: when the history head is blank, `phaseF2`
writes the descriptor `step q a` there and moves to `C q'`. -/
theorem phaseF2_step_S2 (M₀ : KMachine Γ Λ ι) (q : Λ) (a : ι → Γ)
    (T : ι ⊕ Fin 1 → Tape (BennettAlph2 Γ Λ ι)) {q' : Λ} {st : KStmt Γ ι}
    (hr : M₀ q a = some (q', st))
    (hblank : (T (Sum.inr 0)).1 = (Sum.inl default : BennettAlph2 Γ Λ ι)) :
    kstep (phaseF2 M₀) ⟨.S2 q a, T⟩ = some ⟨.C q',
      fun i => match i with
        | Sum.inl j => T (Sum.inl j)
        | Sum.inr _ => (T (Sum.inr 0)).write (Sum.inr (HistEntry2.step q a))⟩ := by
  have hread : headsV T (Sum.inr (0 : Fin 1)) = (Sum.inl default : BennettAlph2 Γ Λ ι) := hblank
  simp only [kstep, phaseF2, hr, hread, ↓reduceIte, Option.map_some]
  refine congrArg some ?_
  refine congr (congrArg KCfg.mk rfl) ?_
  funext i
  cases i with
  | inl j => simp [KStmt.apply, headsV, Tape.write_self]
  | inr k => fin_cases k; simp [KStmt.apply]

/-- Forward `A1 → S`, write rule: `phaseF2` reads the work heads
`a = projHeads (headsV T)`, writes the new symbols `b'` on the work banks, keeps
the history, and carries `(q, a)` into `S q a`.  (Enabled by the `projHeads`
refactor of `phaseF2`.) -/
theorem phaseF2_A1_write (M₀ : KMachine Γ Λ ι) (q : Λ)
    (T : ι ⊕ Fin 1 → Tape (BennettAlph2 Γ Λ ι)) {q' : Λ} {b' : ι → Γ}
    (hr : M₀ q (projHeads (headsV T)) = some (q', KStmt.write b')) :
    kstep (phaseF2 M₀) ⟨.A1 q, T⟩ = some ⟨.S q (projHeads (headsV T)),
      fun i => match i with
        | Sum.inl j => (T (Sum.inl j)).write (Sum.inl (b' j))
        | Sum.inr k => T (Sum.inr k)⟩ := by
  simp only [kstep, phaseF2, hr, Option.map_some]
  refine congrArg some ?_
  refine congr (congrArg KCfg.mk rfl) ?_
  funext i; cases i with
  | inl j => simp [KStmt.apply]
  | inr k => simp [KStmt.apply, headsV, Tape.write_self]

/-- Forward `A1 → S`, move/perm rule: the work banks are left unchanged (an
identity write); `(q, a)` is carried into `S q a`. -/
theorem phaseF2_A1_id (M₀ : KMachine Γ Λ ι) (q : Λ)
    (T : ι ⊕ Fin 1 → Tape (BennettAlph2 Γ Λ ι)) {q' : Λ} {stmt : KStmt Γ ι}
    (hr : M₀ q (projHeads (headsV T)) = some (q', stmt))
    (hns : ∀ b', stmt ≠ KStmt.write b') :
    kstep (phaseF2 M₀) ⟨.A1 q, T⟩ = some ⟨.S q (projHeads (headsV T)), T⟩ := by
  have hid : (KStmt.write (headsV T)).apply T = T := by
    funext i; simp [KStmt.apply, headsV, Tape.write_self]
  cases stmt with
  | write b' => exact absurd rfl (hns b')
  | move d =>
    simp only [kstep, phaseF2, hr, Option.map_some]
    exact congrArg some (congr (congrArg KCfg.mk rfl) hid)
  | perm π =>
    simp only [kstep, phaseF2, hr, Option.map_some]
    exact congrArg some (congr (congrArg KCfg.mk rfl) hid)

/-! ### Reverse single-step lemmas (no `sorry`) -/

/-- Reverse `RStart → RB`: move the history head one step left, keep the work. -/
theorem phaseU2_step_RStart (M₀ : KMachine Γ Λ ι)
    (T : ι ⊕ Fin 1 → Tape (BennettAlph2 Γ Λ ι)) :
    kstep (phaseU2 M₀) ⟨.RStart, T⟩ = some ⟨.RB,
      fun i => match i with
        | Sum.inl j => T (Sum.inl j)
        | Sum.inr k => (T (Sum.inr k)).move Dir.left⟩ := by
  simp only [kstep, phaseU2, Option.map_some]
  refine congrArg some ?_
  refine congr (congrArg KCfg.mk rfl) ?_
  funext i; cases i <;> simp [KStmt.apply]

/-- Reverse `RB → RC`: when the history head holds a descriptor `step q a`,
erase it (write the work blank on the history cell) and carry `(q, a)`. -/
theorem phaseU2_step_RB_desc (M₀ : KMachine Γ Λ ι) (q : Λ) (a : ι → Γ)
    (T : ι ⊕ Fin 1 → Tape (BennettAlph2 Γ Λ ι))
    (hh : (T (Sum.inr 0)).1 = Sum.inr (HistEntry2.step q a)) :
    kstep (phaseU2 M₀) ⟨.RB, T⟩ = some ⟨.RC q a,
      fun i => match i with
        | Sum.inl j => T (Sum.inl j)
        | Sum.inr _ => (T (Sum.inr 0)).write (Sum.inl default)⟩ := by
  have hread : headsV T (Sum.inr (0 : Fin 1)) = Sum.inr (HistEntry2.step q a) := hh
  simp only [kstep, phaseU2, hread, Option.map_some]
  refine congrArg some ?_
  refine congr (congrArg KCfg.mk rfl) ?_
  funext i
  cases i with
  | inl j => simp [KStmt.apply, headsV, Tape.write_self]
  | inr k => fin_cases k; simp [KStmt.apply]

/-- Reverse `RC → RD`, write rule: undo the (no-op) forward `S` move; tapes
unchanged. -/
theorem phaseU2_RC_write (M₀ : KMachine Γ Λ ι) (q : Λ) (a : ι → Γ)
    (T : ι ⊕ Fin 1 → Tape (BennettAlph2 Γ Λ ι)) {q' : Λ} {b' : ι → Γ}
    (hr : M₀ q a = some (q', KStmt.write b')) :
    kstep (phaseU2 M₀) ⟨.RC q a, T⟩ = some ⟨.RD q a, T⟩ := by
  have hid : (KStmt.move (fun _ : ι ⊕ Fin 1 => none)).apply T = T := by
    funext i; simp [KStmt.apply]
  simp only [kstep, phaseU2, hr, Option.map_some]
  exact congrArg some (congr (congrArg KCfg.mk rfl) hid)

/-- Reverse `RC → RD`, move rule: move the work banks by `revMap d` (undoing the
forward move `d`). -/
theorem phaseU2_RC_move (M₀ : KMachine Γ Λ ι) (q : Λ) (a : ι → Γ)
    (T : ι ⊕ Fin 1 → Tape (BennettAlph2 Γ Λ ι)) {q' : Λ} {d : ι → Option Dir}
    (hr : M₀ q a = some (q', KStmt.move d)) :
    kstep (phaseU2 M₀) ⟨.RC q a, T⟩ = some ⟨.RD q a,
      (KStmt.move (fun i => match i with
        | Sum.inl j => (d j).map dirRev | Sum.inr _ => none)).apply T⟩ := by
  simp only [kstep, phaseU2, hr, Option.map_some]

/-- Reverse `RC → RD`, perm rule: permute the work banks by `π⁻¹`. -/
theorem phaseU2_RC_perm (M₀ : KMachine Γ Λ ι) (q : Λ) (a : ι → Γ)
    (T : ι ⊕ Fin 1 → Tape (BennettAlph2 Γ Λ ι)) {q' : Λ} {π : Equiv.Perm ι}
    (hr : M₀ q a = some (q', KStmt.perm π)) :
    kstep (phaseU2 M₀) ⟨.RC q a, T⟩ = some ⟨.RD q a,
      (KStmt.perm (Equiv.sumCongr π⁻¹ (Equiv.refl (Fin 1)))).apply T⟩ := by
  simp only [kstep, phaseU2, hr, Option.map_some]

/-- Reverse `RD → RStart`, write rule: restore the old work heads `a` (undoing
the forward `A1` write). -/
theorem phaseU2_RD_write (M₀ : KMachine Γ Λ ι) (q : Λ) (a : ι → Γ)
    (T : ι ⊕ Fin 1 → Tape (BennettAlph2 Γ Λ ι)) {q' : Λ} {b' : ι → Γ}
    (hr : M₀ q a = some (q', KStmt.write b')) :
    kstep (phaseU2 M₀) ⟨.RD q a, T⟩ = some ⟨.RStart,
      fun i => match i with
        | Sum.inl j => (T (Sum.inl j)).write (Sum.inl (a j))
        | Sum.inr k => T (Sum.inr k)⟩ := by
  simp only [kstep, phaseU2, hr, Option.map_some]
  refine congrArg some ?_
  refine congr (congrArg KCfg.mk rfl) ?_
  funext i; cases i with
  | inl j => simp [KStmt.apply]
  | inr k => simp [KStmt.apply, headsV, Tape.write_self]

/-- Reverse `RD → RStart`, move/perm rule: identity write (undoing the forward
`A1` identity write). -/
theorem phaseU2_RD_id (M₀ : KMachine Γ Λ ι) (q : Λ) (a : ι → Γ)
    (T : ι ⊕ Fin 1 → Tape (BennettAlph2 Γ Λ ι)) {q' : Λ} {stmt : KStmt Γ ι}
    (hr : M₀ q a = some (q', stmt))
    (hns : ∀ b', stmt ≠ KStmt.write b') :
    kstep (phaseU2 M₀) ⟨.RD q a, T⟩ = some ⟨.RStart, T⟩ := by
  have hid : (KStmt.write (headsV T)).apply T = T := by
    funext i; simp [KStmt.apply, headsV, Tape.write_self]
  cases stmt with
  | write b' => exact absurd rfl (hns b')
  | move d =>
    simp only [kstep, phaseU2, hr, Option.map_some]
    exact congrArg some (congr (congrArg KCfg.mk rfl) hid)
  | perm π =>
    simp only [kstep, phaseU2, hr, Option.map_some]
    exact congrArg some (congr (congrArg KCfg.mk rfl) hid)

/-! ### Macro-step composition -/

/-- For a well-formed work bank, the projected head re-injects to the actual
head: `Sum.inl (projHeads (headsV T) j) = (T (Sum.inl j)).head`. -/
theorem projHeads_inl_of_WF {T : ι ⊕ Fin 1 → Tape (BennettAlph2 Γ Λ ι)}
    (hWF : WFtapes T) (j : ι) :
    (Sum.inl (projHeads (headsV T) j) : BennettAlph2 Γ Λ ι) = (T (Sum.inl j)).head := by
  obtain ⟨x, hx⟩ := (hWF j).head_inl
  simp only [projHeads, headsV, hx]

/-- A single forward step embeds into `Reaches`. -/
theorem reaches_of_kstep {M : KMachine Γ Λ ι} {c c' : KCfg Γ Λ ι}
    (h : kstep M c = some c') : StateTransition.Reaches (kstep M) c c' :=
  Relation.ReflTransGen.single (Option.mem_def.mpr h)

/-- **Macro step, write rule.**  One forward macro `A1 q → … → A1 q'` (write
case) advances to `T1`; the reverse macro on `T1` recovers `T`.  Needs the
history head blank and the work banks well-formed. -/
theorem phaseF2_macro_write (M₀ : KMachine Γ Λ ι) (q : Λ)
    (T : ι ⊕ Fin 1 → Tape (BennettAlph2 Γ Λ ι))
    (hWF : WFtapes T)
    (hblank : (T (Sum.inr 0)).head = (Sum.inl default : BennettAlph2 Γ Λ ι))
    {q' : Λ} {b' : ι → Γ}
    (hr : M₀ q (projHeads (headsV T)) = some (q', KStmt.write b')) :
    ∃ T1, reachesN (phaseF2 M₀) 4 ⟨.A1 q, T⟩ ⟨.A1 q', T1⟩ ∧
          StateTransition.Reaches (kstep (phaseU2 M₀)) ⟨.RStart, T1⟩ ⟨.RStart, T⟩ ∧
          WFtapes T1 := by
  classical
  set a := projHeads (headsV T) with ha
  let TA1 : ι ⊕ Fin 1 → Tape (BennettAlph2 Γ Λ ι) :=
    fun i => match i with
      | Sum.inl j => (T (Sum.inl j)).write (Sum.inl (b' j))
      | Sum.inr k => T (Sum.inr k)
  let TS2 : ι ⊕ Fin 1 → Tape (BennettAlph2 Γ Λ ι) :=
    fun i => match i with
      | Sum.inl j => TA1 (Sum.inl j)
      | Sum.inr _ => (TA1 (Sum.inr 0)).write (Sum.inr (HistEntry2.step q a))
  let T1 : ι ⊕ Fin 1 → Tape (BennettAlph2 Γ Λ ι) :=
    fun i => match i with
      | Sum.inl j => TS2 (Sum.inl j)
      | Sum.inr k => (TS2 (Sum.inr k)).move Dir.right
  have hTA1blank : (TA1 (Sum.inr 0)).head = (Sum.inl default : BennettAlph2 Γ Λ ι) := hblank
  refine ⟨T1, ?_, ?_, ?_⟩
  · -- forward reachesN 4
    have r0 : reachesN (phaseF2 M₀) 0 (⟨.A1 q, T⟩ : KCfg _ _ _) ⟨.A1 q, T⟩ := rfl
    exact reachesN_snoc _ (reachesN_snoc _ (reachesN_snoc _
      (reachesN_snoc _ r0 (phaseF2_A1_write M₀ q T hr))
      (phaseF2_S_write M₀ q a TA1 hr))
      (phaseF2_step_S2 M₀ q a TA1 hr hTA1blank))
      (phaseF2_step_C M₀ q' TS2)
  · -- reverse Reaches
    let T1L : ι ⊕ Fin 1 → Tape (BennettAlph2 Γ Λ ι) :=
      fun i => match i with
        | Sum.inl j => T1 (Sum.inl j)
        | Sum.inr k => (T1 (Sum.inr k)).move Dir.left
    let T1RB : ι ⊕ Fin 1 → Tape (BennettAlph2 Γ Λ ι) :=
      fun i => match i with
        | Sum.inl j => T1L (Sum.inl j)
        | Sum.inr _ => (T1L (Sum.inr 0)).write (Sum.inl default)
    have hT1L0 : T1L (Sum.inr 0)
        = (T (Sum.inr 0)).write (Sum.inr (HistEntry2.step q a)) := by
      show ((((T (Sum.inr 0)).write (Sum.inr (HistEntry2.step q a))).move Dir.right).move Dir.left)
          = _
      exact tape_move_dirRev _ Dir.right
    have hhd : (T1L (Sum.inr 0)).head = Sum.inr (HistEntry2.step q a) := by
      rw [hT1L0]; rfl
    have hfin : (fun i => match i with
        | Sum.inl j => (T1RB (Sum.inl j)).write (Sum.inl (a j))
        | Sum.inr k => T1RB (Sum.inr k)) = T := by
      funext i
      cases i with
      | inl j =>
        show ((T (Sum.inl j)).write (Sum.inl (b' j))).write (Sum.inl (a j)) = T (Sum.inl j)
        rw [tape_write_write, ha, projHeads_inl_of_WF hWF j, Tape.write_self]
      | inr k =>
        fin_cases k
        show (T1L (Sum.inr 0)).write (Sum.inl default) = T (Sum.inr 0)
        rw [hT1L0, tape_write_write, ← hblank, Tape.write_self]
    refine (reaches_of_kstep (phaseU2_step_RStart M₀ T1)).trans ?_
    refine (reaches_of_kstep (phaseU2_step_RB_desc M₀ q a T1L hhd)).trans ?_
    refine (reaches_of_kstep (phaseU2_RC_write M₀ q a T1RB hr)).trans ?_
    have hstep := phaseU2_RD_write M₀ q a T1RB hr
    rw [hfin] at hstep
    exact reaches_of_kstep hstep
  · -- WFtapes T1
    intro j
    show WFtape ((T (Sum.inl j)).write (Sum.inl (b' j)))
    exact (hWF j).write_inl (b' j)

/-- **Macro step, move rule.**  Same as the write case but `A1` is an identity
write, the work banks are moved by `d` (undone by `move_cancel`), and `RD` is an
identity. -/
theorem phaseF2_macro_move (M₀ : KMachine Γ Λ ι) (q : Λ)
    (T : ι ⊕ Fin 1 → Tape (BennettAlph2 Γ Λ ι))
    (hWF : WFtapes T)
    (hblank : (T (Sum.inr 0)).head = (Sum.inl default : BennettAlph2 Γ Λ ι))
    {q' : Λ} {d : ι → Option Dir}
    (hr : M₀ q (projHeads (headsV T)) = some (q', KStmt.move d)) :
    ∃ T1, reachesN (phaseF2 M₀) 4 ⟨.A1 q, T⟩ ⟨.A1 q', T1⟩ ∧
          StateTransition.Reaches (kstep (phaseU2 M₀)) ⟨.RStart, T1⟩ ⟨.RStart, T⟩ ∧
          WFtapes T1 := by
  classical
  set a := projHeads (headsV T) with ha
  -- df : the doubled-index move; TS = work moved
  let df : ι ⊕ Fin 1 → Option Dir := fun i => match i with | Sum.inl j => d j | Sum.inr _ => none
  let TS : ι ⊕ Fin 1 → Tape (BennettAlph2 Γ Λ ι) := (KStmt.move df).apply T
  let TSd2 : ι ⊕ Fin 1 → Tape (BennettAlph2 Γ Λ ι) :=
    fun i => match i with
      | Sum.inl j => TS (Sum.inl j)
      | Sum.inr _ => (TS (Sum.inr 0)).write (Sum.inr (HistEntry2.step q a))
  let T1 : ι ⊕ Fin 1 → Tape (BennettAlph2 Γ Λ ι) :=
    fun i => match i with
      | Sum.inl j => TSd2 (Sum.inl j)
      | Sum.inr k => (TSd2 (Sum.inr k)).move Dir.right
  have hTSblank : (TS (Sum.inr 0)).head = (Sum.inl default : BennettAlph2 Γ Λ ι) := by
    show ((KStmt.move df).apply T (Sum.inr 0)).head = _
    simp only [KStmt.apply]; exact hblank
  refine ⟨T1, ?_, ?_, ?_⟩
  · -- forward reachesN 4
    have r0 : reachesN (phaseF2 M₀) 0 (⟨.A1 q, T⟩ : KCfg _ _ _) ⟨.A1 q, T⟩ := rfl
    exact reachesN_snoc _ (reachesN_snoc _ (reachesN_snoc _
      (reachesN_snoc _ r0 (phaseF2_A1_id M₀ q T hr (by rintro b ⟨⟩)))
      (phaseF2_S_move M₀ q a T hr))
      (phaseF2_step_S2 M₀ q a TS hr hTSblank))
      (phaseF2_step_C M₀ q' TSd2)
  · -- reverse Reaches
    let T1L : ι ⊕ Fin 1 → Tape (BennettAlph2 Γ Λ ι) :=
      fun i => match i with
        | Sum.inl j => T1 (Sum.inl j)
        | Sum.inr k => (T1 (Sum.inr k)).move Dir.left
    let T1RB : ι ⊕ Fin 1 → Tape (BennettAlph2 Γ Λ ι) :=
      fun i => match i with
        | Sum.inl j => T1L (Sum.inl j)
        | Sum.inr _ => (T1L (Sum.inr 0)).write (Sum.inl default)
    have hT1L0 : T1L (Sum.inr 0)
        = (T (Sum.inr 0)).write (Sum.inr (HistEntry2.step q a)) := by
      show ((((T (Sum.inr 0)).write (Sum.inr (HistEntry2.step q a))).move Dir.right).move Dir.left)
          = _
      exact tape_move_dirRev _ Dir.right
    have hhd : (T1L (Sum.inr 0)).head = Sum.inr (HistEntry2.step q a) := by rw [hT1L0]; rfl
    have hT1RB : T1RB = (KStmt.move df).apply T := by
      funext i
      cases i with
      | inl j => rfl
      | inr k =>
        fin_cases k
        show (T1L (Sum.inr 0)).write (Sum.inl default) = (KStmt.move df).apply T (Sum.inr 0)
        rw [hT1L0, tape_write_write, ← hblank, Tape.write_self]
        rfl
    have hfin : (KStmt.move (fun i => match i with
        | Sum.inl j => (d j).map dirRev | Sum.inr _ => none)).apply T1RB = T := by
      rw [hT1RB]
      have hrev : (fun i => match i with
          | Sum.inl j => (d j).map dirRev | Sum.inr (_ : Fin 1) => none)
          = revMap df := by
        funext i; cases i <;> rfl
      rw [hrev]
      exact move_cancel T df
    refine (reaches_of_kstep (phaseU2_step_RStart M₀ T1)).trans ?_
    refine (reaches_of_kstep (phaseU2_step_RB_desc M₀ q a T1L hhd)).trans ?_
    refine (reaches_of_kstep (phaseU2_RC_move M₀ q a T1RB hr)).trans ?_
    rw [hfin]
    exact reaches_of_kstep (phaseU2_RD_id M₀ q a T hr (by rintro b ⟨⟩))
  · -- WFtapes T1
    intro j
    show WFtape (TS (Sum.inl j))
    obtain ⟨x, hx⟩ := (hWF j).head_inl
    rcases hd : d j with _ | dir
    · show WFtape ((KStmt.move df).apply T (Sum.inl j))
      simp only [KStmt.apply, df, hd]; exact hWF j
    · show WFtape ((KStmt.move df).apply T (Sum.inl j))
      simp only [KStmt.apply, df, hd]; exact (hWF j).move' dir

/-- **Macro step, perm rule.**  Like the move case, with the work banks permuted
by `π` (undone by `perm_cancel`); `A1` and `RD` are identity writes. -/
theorem phaseF2_macro_perm (M₀ : KMachine Γ Λ ι) (q : Λ)
    (T : ι ⊕ Fin 1 → Tape (BennettAlph2 Γ Λ ι))
    (hWF : WFtapes T)
    (hblank : (T (Sum.inr 0)).head = (Sum.inl default : BennettAlph2 Γ Λ ι))
    {q' : Λ} {π : Equiv.Perm ι}
    (hr : M₀ q (projHeads (headsV T)) = some (q', KStmt.perm π)) :
    ∃ T1, reachesN (phaseF2 M₀) 4 ⟨.A1 q, T⟩ ⟨.A1 q', T1⟩ ∧
          StateTransition.Reaches (kstep (phaseU2 M₀)) ⟨.RStart, T1⟩ ⟨.RStart, T⟩ ∧
          WFtapes T1 := by
  classical
  set a := projHeads (headsV T) with ha
  let σ : Equiv.Perm (ι ⊕ Fin 1) := Equiv.sumCongr π (Equiv.refl (Fin 1))
  let TS : ι ⊕ Fin 1 → Tape (BennettAlph2 Γ Λ ι) := (KStmt.perm σ).apply T
  let TSd2 : ι ⊕ Fin 1 → Tape (BennettAlph2 Γ Λ ι) :=
    fun i => match i with
      | Sum.inl j => TS (Sum.inl j)
      | Sum.inr _ => (TS (Sum.inr 0)).write (Sum.inr (HistEntry2.step q a))
  let T1 : ι ⊕ Fin 1 → Tape (BennettAlph2 Γ Λ ι) :=
    fun i => match i with
      | Sum.inl j => TSd2 (Sum.inl j)
      | Sum.inr k => (TSd2 (Sum.inr k)).move Dir.right
  have hTSir : TS (Sum.inr 0) = T (Sum.inr 0) := by
    show T (σ.symm (Sum.inr 0)) = _
    congr 1
  have hTSblank : (TS (Sum.inr 0)).head = (Sum.inl default : BennettAlph2 Γ Λ ι) := by
    rw [hTSir]; exact hblank
  refine ⟨T1, ?_, ?_, ?_⟩
  · -- forward reachesN 4
    have r0 : reachesN (phaseF2 M₀) 0 (⟨.A1 q, T⟩ : KCfg _ _ _) ⟨.A1 q, T⟩ := rfl
    exact reachesN_snoc _ (reachesN_snoc _ (reachesN_snoc _
      (reachesN_snoc _ r0 (phaseF2_A1_id M₀ q T hr (by rintro b ⟨⟩)))
      (phaseF2_S_perm M₀ q a T hr))
      (phaseF2_step_S2 M₀ q a TS hr hTSblank))
      (phaseF2_step_C M₀ q' TSd2)
  · -- reverse Reaches
    let T1L : ι ⊕ Fin 1 → Tape (BennettAlph2 Γ Λ ι) :=
      fun i => match i with
        | Sum.inl j => T1 (Sum.inl j)
        | Sum.inr k => (T1 (Sum.inr k)).move Dir.left
    let T1RB : ι ⊕ Fin 1 → Tape (BennettAlph2 Γ Λ ι) :=
      fun i => match i with
        | Sum.inl j => T1L (Sum.inl j)
        | Sum.inr _ => (T1L (Sum.inr 0)).write (Sum.inl default)
    have hT1L0 : T1L (Sum.inr 0)
        = (T (Sum.inr 0)).write (Sum.inr (HistEntry2.step q a)) := by
      have e1 : T1L (Sum.inr 0) = (TS (Sum.inr 0)).write (Sum.inr (HistEntry2.step q a)) := by
        show ((((TS (Sum.inr 0)).write (Sum.inr (HistEntry2.step q a))).move Dir.right).move Dir.left)
            = _
        exact tape_move_dirRev _ Dir.right
      rw [e1, hTSir]
    have hhd : (T1L (Sum.inr 0)).head = Sum.inr (HistEntry2.step q a) := by rw [hT1L0]; rfl
    have hT1RB : T1RB = (KStmt.perm σ).apply T := by
      funext i
      cases i with
      | inl j => rfl
      | inr k =>
        fin_cases k
        show (T1L (Sum.inr 0)).write (Sum.inl default) = (KStmt.perm σ).apply T (Sum.inr 0)
        rw [hT1L0, tape_write_write, ← hblank, Tape.write_self, ← hTSir]
    have hfin : (KStmt.perm (Equiv.sumCongr π⁻¹ (Equiv.refl (Fin 1)))).apply T1RB = T := by
      rw [hT1RB]
      have hsymm : (Equiv.sumCongr π⁻¹ (Equiv.refl (Fin 1)) : Equiv.Perm (ι ⊕ Fin 1)) = σ⁻¹ := by
        ext x; cases x <;> rfl
      rw [hsymm]
      exact perm_cancel T σ
    refine (reaches_of_kstep (phaseU2_step_RStart M₀ T1)).trans ?_
    refine (reaches_of_kstep (phaseU2_step_RB_desc M₀ q a T1L hhd)).trans ?_
    refine (reaches_of_kstep (phaseU2_RC_perm M₀ q a T1RB hr)).trans ?_
    rw [hfin]
    exact reaches_of_kstep (phaseU2_RD_id M₀ q a T hr (by rintro b ⟨⟩))
  · -- WFtapes T1
    intro j
    show WFtape (TS (Sum.inl j))
    show WFtape (T (σ.symm (Sum.inl j)))
    have : σ.symm (Sum.inl j) = Sum.inl (π.symm j) := by
      show (Equiv.sumCongr π (Equiv.refl (Fin 1))).symm (Sum.inl j) = _
      rw [Equiv.sumCongr_symm]; rfl
    rw [this]; exact hWF (π.symm j)

/-! ### The SemInverse goal (Stage 1c)

PROOF PLAN for `phaseF2_uncompute_fwd` (the macro recursion).  Decompose into
single-step lemmas, each built like `phaseU2_terminal` / `phaseF2_step_C`
(compute the tape effect as an `htapes` `have`, then
`simp [kstep, phaseF2/phaseU2, ...]`):

  forward macro (one M₀ step, `M₀ q a = some (q', stmt)`):
    A1: write the work effect of `stmt` (or identity for move/perm)   [3 cases]
    S : do the work move/perm (or no-op)                              [3 cases]
    S2: write descriptor `step q a` at the history head (head blank)
    C : advance the history head right                                [phaseF2_step_C]
  reverse macro (mirror), on the forward image:
    RStart: move history left -- lands on the cell C just left of, i.e. the
            descriptor S2 wrote (uses `tape_move_dirRev` to cancel C's right move)
    RB    : read that descriptor, erase it (write blank)
    RC    : undo the work move/perm (`move_cancel`, `perm_cancel`) or no-op
    RD    : restore the old work heads `a` (`write_write_cancel`) or identity

Then `reverse_macro : ⟨A1 q, T⟩ →⁴ ⟨A1 q', T'⟩ ⟹ ⟨RStart, T'⟩ →⁴ ⟨RStart, T⟩`,
glued by induction on the number of forward macro-steps with `phaseU2_terminal`
as the base case (history head back past 0).  The induction extracts the
macro-step structure from a `phaseF2` run using the `HistInv`/`SHInv`/`NoHaltInv`
invariants of `BennettWF.lean` (halting is at `A1`, every `A1` came from a `C`,
etc.).

The frontier is isolated to a SINGLE obligation, the *forward* leg
`phaseF2_uncompute_fwd`: every `phaseF2`-output reverses under `phaseU2`.  With
the domain taken to be the image of `phaseF2`, the *backward* leg is then FREE
-- it follows from the forward leg and the determinism of `ktapeSem`
(`Part.mem_unique`).  So `phaseF2_semInverse` adds no new `sorry` beyond the
trace correspondence. -/

/-! **Stage 1c.**  Every single step of both macros is mechanised; the forward
leg `phaseF2_uncompute_fwd` is now assembled from the three macro lemmas, a
prefix-cancel, and a strong-induction reverse simulation, all `sorry`-free. -/

/-- Determinism / prefix-cancel: a forward `a`-step prefix of an `n`-step run
that ends at a halting config leaves an `(n-a)`-step run from the prefix
endpoint.  (For `n < a` the hypotheses are contradictory, handled internally.) -/
theorem reachesN_cancel (M : KMachine Γ Λ ι) :
    ∀ {a n : ℕ} {c m c' : KCfg Γ Λ ι},
      reachesN M a c m → reachesN M n c c' → kstep M c' = none →
      reachesN M (n - a) m c' := by
  intro a
  induction a with
  | zero => intro n c m c' h1 h2 _; simp only [reachesN] at h1; subst h1; simpa using h2
  | succ a ih =>
    intro n c m c' h1 h2 hhalt
    simp only [reachesN] at h1
    obtain ⟨c1, hc1, hr1⟩ := h1
    cases n with
    | zero =>
      simp only [reachesN] at h2; subst h2; rw [hhalt] at hc1; exact absurd hc1 (by simp)
    | succ n' =>
      simp only [reachesN] at h2
      obtain ⟨c2, hc2, hr2⟩ := h2
      have hcc : c1 = c2 := by rw [hc1] at hc2; exact Option.some.inj hc2
      subst hcc
      simpa using ih hr1 hr2 hhalt

/-- Macro step, dispatched on the rule kind (combines the three macro lemmas). -/
theorem phaseF2_macro (M₀ : KMachine Γ Λ ι) (q : Λ)
    (T : ι ⊕ Fin 1 → Tape (BennettAlph2 Γ Λ ι))
    (hWF : WFtapes T)
    (hblank : (T (Sum.inr 0)).head = (Sum.inl default : BennettAlph2 Γ Λ ι))
    {q' : Λ} {stmt : KStmt Γ ι}
    (hr : M₀ q (projHeads (headsV T)) = some (q', stmt)) :
    ∃ T1, reachesN (phaseF2 M₀) 4 ⟨.A1 q, T⟩ ⟨.A1 q', T1⟩ ∧
          StateTransition.Reaches (kstep (phaseU2 M₀)) ⟨.RStart, T1⟩ ⟨.RStart, T⟩ ∧
          WFtapes T1 := by
  cases stmt with
  | write b' => exact phaseF2_macro_write M₀ q T hWF hblank hr
  | move d => exact phaseF2_macro_move M₀ q T hWF hblank hr
  | perm π => exact phaseF2_macro_perm M₀ q T hWF hblank hr

/-- **Reverse simulation of a forward run.**  If `phaseF2` runs from a WF
`A1 q` config satisfying `HistInv` to a halting `chalt` in `n` steps, then
`phaseU2` runs from `⟨RStart, chalt.tapes⟩` back to `⟨RStart, T⟩`.  Strong
induction on `n`, peeling one macro at a time onto `HistInv_reachesN`. -/
theorem phaseF2_rev_sim (M₀ : KMachine Γ Λ ι) :
    ∀ (n : ℕ) (q : Λ) (T : ι ⊕ Fin 1 → Tape (BennettAlph2 Γ Λ ι))
      (chalt : KCfg (BennettAlph2 Γ Λ ι) (BennettState2 Γ Λ ι) (ι ⊕ Fin 1)),
      WFtapes T → HistInv ⟨.A1 q, T⟩ →
      reachesN (phaseF2 M₀) n ⟨.A1 q, T⟩ chalt → kstep (phaseF2 M₀) chalt = none →
      StateTransition.Reaches (kstep (phaseU2 M₀)) ⟨.RStart, chalt.tapes⟩ ⟨.RStart, T⟩ := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro q T chalt hWF hHI hrun hhalt
    have hblank : (T (Sum.inr 0)).head = (Sum.inl default : BennettAlph2 Γ Λ ι) := hHI.2
    rcases hM : M₀ q (projHeads (headsV T)) with _ | ⟨q', stmt⟩
    · -- immediate halt
      have hstep0 : kstep (phaseF2 M₀) ⟨.A1 q, T⟩ = none := by
        simp only [kstep, phaseF2, hM]; rfl
      cases n with
      | zero => simp only [reachesN] at hrun; subst hrun; exact Relation.ReflTransGen.refl
      | succ m =>
        simp only [reachesN] at hrun; obtain ⟨c'', hc'', _⟩ := hrun
        rw [hstep0] at hc''; exact absurd hc'' (by simp)
    · -- macro step
      obtain ⟨T1, hfwd4, hrev, hWF1⟩ := phaseF2_macro M₀ q T hWF hblank hM
      have hsub : reachesN (phaseF2 M₀) (n - 4) ⟨.A1 q', T1⟩ chalt :=
        reachesN_cancel (phaseF2 M₀) hfwd4 hrun hhalt
      have hn1 : 0 < n := by
        rcases n with _ | m
        · simp only [reachesN] at hrun; subst hrun
          simp only [reachesN] at hfwd4; obtain ⟨c1, hc1, _⟩ := hfwd4
          rw [hc1] at hhalt; exact absurd hhalt (by simp)
        · omega
      have hlt : n - 4 < n := Nat.sub_lt hn1 (by norm_num)
      have hHI1 : HistInv ⟨.A1 q', T1⟩ := HistInv_reachesN M₀ hfwd4 hHI
      exact (ih (n - 4) hlt q' T1 chalt hWF1 hHI1 hsub hhalt).trans hrev

/-- **Forward leg of `SemInverse` (Stage 1c, no `sorry`).**  Every output of
`phaseF2` on a WF, blank-history input `X` is reversed by `phaseU2` back to `X`.
The WF + blank-history hypotheses are necessary: on a non-WF input the reverse
`RD`-restore would land on `default` rather than the junk head, so the
unrestricted `∀ X` form is false (matching the prototype's domain finding). -/
theorem phaseF2_uncompute_fwd (M₀ : KMachine Γ Λ ι) (q₀ : Λ)
    (X Y : ι ⊕ Fin 1 → Tape (BennettAlph2 Γ Λ ι))
    (hWF : WFtapes X) (hbl : X (Sum.inr 0) = default)
    (hY : Y ∈ ktapeSem (phaseF2 M₀) (BennettState2.A1 q₀) X) :
    X ∈ ktapeSem (phaseU2 M₀) UncompState.RStart Y := by
  classical
  obtain ⟨chalt, hchalt, rfl⟩ := (Part.mem_map_iff _).mp hY
  obtain ⟨hreach, hhalt⟩ := StateTransition.mem_eval.mp hchalt
  obtain ⟨n, hrun⟩ := reaches_to_reachesN _ hreach
  have hHI : HistInv ⟨.A1 q₀, X⟩ := HistInv_of_blank_hist hbl
  have hrev := phaseF2_rev_sim M₀ n q₀ X chalt hWF hHI hrun hhalt
  -- terminal run ⟨RStart, X⟩ →* ⟨RFin, X⟩
  have hterm : X ∈ ktapeSem (phaseU2 M₀) UncompState.RStart X := by
    apply phaseU2_terminal
    rw [hbl]; rfl
  obtain ⟨cfg, hcfg, hcfgX⟩ := (Part.mem_map_iff _).mp hterm
  obtain ⟨htreach, hthalt⟩ := StateTransition.mem_eval.mp hcfg
  exact (Part.mem_map_iff _).mpr
    ⟨cfg, StateTransition.mem_eval.mpr ⟨hrev.trans htreach, hthalt⟩, hcfgX⟩

/-- The input domain: WF, blank-history tapes. -/
def WFblank (X : ι ⊕ Fin 1 → Tape (BennettAlph2 Γ Λ ι)) : Prop :=
  WFtapes X ∧ X (Sum.inr 0) = default

/-- The reachable-output domain: image of `phaseF2` from `A1 q₀` on `WFblank`
inputs. -/
def reachableOutput (M₀ : KMachine Γ Λ ι) (q₀ : Λ)
    (Y : ι ⊕ Fin 1 → Tape (BennettAlph2 Γ Λ ι)) : Prop :=
  ∃ X, WFblank X ∧ Y ∈ ktapeSem (phaseF2 M₀) (BennettState2.A1 q₀) X

/-- **Stage 1c result (no `sorry`).**  `phaseU2 M₀` is a `SemInverse` of
`phaseF2 M₀`: `fwd` on the `WFblank` input domain is `phaseF2_uncompute_fwd`;
`bwd` on the reachable-output domain follows from `fwd` + determinism of
`ktapeSem` (the `phaseU2`-preimage is forced to be the `reachableOutput`
witness). -/
theorem phaseF2_semInverse (M₀ : KMachine Γ Λ ι) (q₀ : Λ) :
    SemInverse (phaseF2 M₀) (phaseU2 M₀)
      (BennettState2.A1 q₀) UncompState.RStart
      WFblank (reachableOutput M₀ q₀) where
  fwd := fun X Y hX hY => phaseF2_uncompute_fwd M₀ q₀ X Y hX.1 hX.2 hY
  bwd := by
    rintro X Y ⟨X₀, ⟨hWF₀, hbl₀⟩, hX₀⟩ hXY
    have hX₀' : X₀ ∈ ktapeSem (phaseU2 M₀) UncompState.RStart Y :=
      phaseF2_uncompute_fwd M₀ q₀ X₀ Y hWF₀ hbl₀ hX₀
    have : X = X₀ := Part.mem_unique hXY hX₀'
    rw [this]; exact hX₀

/-- **The U-leg of the Bennett wrapper.**  `phaseF2` inverts `phaseU2` -- the
uncompute machine's semantic inverse is the forward simulator.  Free from
`phaseF2_semInverse` by symmetry; this is the leg `B' = U⁻¹;C⁻¹;F⁻¹` needs for
its outermost component. -/
theorem phaseU2_semInverse (M₀ : KMachine Γ Λ ι) (q₀ : Λ) :
    SemInverse (phaseU2 M₀) (phaseF2 M₀)
      UncompState.RStart (BennettState2.A1 q₀)
      (reachableOutput M₀ q₀) WFblank :=
  (phaseF2_semInverse M₀ q₀).symm

/-! ### Stage 2: assembling the unconditional symmetrisation -/

/-- The trivial bank-swap (identity permutation) computes the identity: it is the
involutory middle leg of the conjugation that preserves the reachable-output
domain. -/
theorem bankSwap_refl_eq (U V : ι ⊕ Fin 1 → Tape (BennettAlph2 Γ Λ ι))
    (hV : V ∈ ktapeSem (bankSwap (Equiv.refl (ι ⊕ Fin 1))) false U) : V = U := by
  obtain ⟨c, hc, rfl⟩ := (Part.mem_map_iff _).mp hV
  obtain ⟨hr, hhalt⟩ := StateTransition.mem_eval.mp hc
  have step1 : kstep (bankSwap (Equiv.refl (ι ⊕ Fin 1))) ⟨false, U⟩ = some ⟨true, U⟩ := by
    simp only [kstep, bankSwap]
    refine congrArg some (congr (congrArg KCfg.mk rfl) ?_)
    funext i; simp [KStmt.apply]
  have halt2 : kstep (bankSwap (Equiv.refl (ι ⊕ Fin 1))) (⟨true, U⟩ : KCfg _ _ _) = none := by
    simp [kstep, bankSwap]
  -- the run from ⟨false, U⟩ halts at ⟨true, U⟩
  rcases Relation.ReflTransGen.cases_head hr with heq | ⟨b, hb, hrest⟩
  · rw [← heq, step1] at hhalt; exact absurd hhalt (by simp)
  · have hbeq : b = (⟨true, U⟩ : KCfg _ _ _) := by
      rw [Option.mem_def, step1] at hb; exact (Option.some.inj hb).symm
    subst hbeq
    rcases Relation.ReflTransGen.cases_head hrest with heq2 | ⟨b2, hb2, _⟩
    · exact (congrArg KCfg.tapes heq2).symm
    · rw [Option.mem_def, halt2] at hb2; exact absurd hb2 (by simp)

/-- **Stage 2 (G1, no `sorry`).**  The conjugate of the (trivial) bank-swap
involution by the Bennett reversibiliser `phaseF2`/`phaseU2` computes a partial
involution on well-formed, blank-history inputs, with NO `KReversible`
hypothesis on `M₀` -- the function-level unconditional involutory-computability
that syntactic reversibility could not provide.  (The swap is the identity here,
so the computed involution is the identity; making it a nontrivial `f` is the
orthogonal G2 / forward-correctness task.) -/
theorem nakano_symmetrisation_unconditional_partial (M₀ : KMachine Γ Λ ι) (q₀ : Λ) :
    IsPartialInvolutionOn
      (seq (seq (phaseF2 M₀) (bankSwap (Equiv.refl (ι ⊕ Fin 1))) false)
        (phaseU2 M₀) UncompState.RStart)
      (Sum.inl (Sum.inl (BennettState2.A1 q₀)))
      WFblank := by
  apply conj_isPartialInvolution
    (involutory_bankSwap (Equiv.refl (ι ⊕ Fin 1)) (by exact Equiv.refl_symm))
    (phaseF2_semInverse M₀ q₀)
  rintro U V ⟨T, hT, hU⟩ hV
  rw [bankSwap_refl_eq U V hV]
  exact ⟨T, hT, hU⟩

/-! ### G2 prep: lifting `M₀` tapes into the descriptor alphabet

Forward correctness (the remaining, reversibility-orthogonal task) says
`phaseF2 M₀` computes `M₀`'s function on the work banks.  Inputs are lifted
through `inlMap` (`Sum.inl`): `liftWork A` puts `Tape.map inlMap (A j)` on work
bank `j` and a blank history.  These lifts are well-formed and blank-history (so
they sit in the `phaseF2_semInverse` input domain), and lifting commutes with
the write/move work operations (`Tape.map_write`/`Tape.map_move`), which is what
a forward-simulation induction (mirroring `phaseF2_rev_sim`) will consume. -/

/-- Lift an `M₀` tape bundle into the descriptor alphabet with a blank history.
The `M₀` argument fixes the otherwise-phantom state type `Λ`. -/
def liftWork (_M₀ : KMachine Γ Λ ι) (A : ι → Tape Γ) :
    ι ⊕ Fin 1 → Tape (BennettAlph2 Γ Λ ι) :=
  fun i => match i with
    | Sum.inl j => Tape.map inlMap (A j)
    | Sum.inr _ => default

theorem liftWork_WF (M₀ : KMachine Γ Λ ι) (A : ι → Tape Γ) :
    WFtapes (liftWork M₀ A) := fun j => ⟨A j, rfl⟩

theorem liftWork_blank (M₀ : KMachine Γ Λ ι) (A : ι → Tape Γ) :
    (liftWork M₀ A) (Sum.inr 0) = default := rfl

theorem liftWork_WFblank (M₀ : KMachine Γ Λ ι) (A : ι → Tape Γ) :
    WFblank (liftWork M₀ A) := ⟨liftWork_WF M₀ A, liftWork_blank M₀ A⟩

/-- Lifting commutes with a work-bank write. -/
theorem liftWork_write (M₀ : KMachine Γ Λ ι) (A : ι → Tape Γ) (j : ι) (γ : Γ) :
    (liftWork M₀ A (Sum.inl j)).write (Sum.inl γ) = Tape.map inlMap ((A j).write γ) :=
  (Tape.map_write inlMap γ (A j)).symm

/-- Lifting commutes with a work-bank move. -/
theorem liftWork_move (M₀ : KMachine Γ Λ ι) (A : ι → Tape Γ) (j : ι) (d : Dir) :
    (liftWork M₀ A (Sum.inl j)).move d = Tape.map inlMap ((A j).move d) :=
  (Tape.map_move inlMap (A j) d).symm

/-- The descriptor simulator reads exactly `M₀`'s heads on a lifted input. -/
theorem projHeads_liftWork (M₀ : KMachine Γ Λ ι) (A : ι → Tape Γ) :
    projHeads (headsV (liftWork M₀ A)) = headsV A := by
  funext i
  have hh : headsV (liftWork M₀ A) (Sum.inl i) = Sum.inl ((A i).1) := by
    show (Tape.map inlMap (A i)).1 = _
    rw [Tape.map_fst]; rfl
  show (match headsV (liftWork M₀ A) (Sum.inl i) with
    | Sum.inl γ => γ | Sum.inr _ => default) = headsV A i
  rw [hh]; rfl

/-- **G2-fwd Step 2 (general config).**  One forward macro on a config `T`
whose work banks are the lift of `A` and whose history head is blank: `phaseF2`
reaches `⟨A1 q', T1⟩` in 4 steps with `T1`'s work banks the lift of `M₀`'s
one-step work effect `stmt.apply A`.  Stated for a general `T` (not just
`liftWork A`) so the forward induction can carry the accumulating history. -/
theorem phaseF2_fwd_macro (M₀ : KMachine Γ Λ ι) (A : ι → Tape Γ)
    (T : ι ⊕ Fin 1 → Tape (BennettAlph2 Γ Λ ι))
    (hwork : ∀ j, T (Sum.inl j) = Tape.map inlMap (A j))
    (hblank : (T (Sum.inr 0)).head = (Sum.inl default : BennettAlph2 Γ Λ ι))
    {q q' : Λ} {stmt : KStmt Γ ι} (hr : M₀ q (headsV A) = some (q', stmt)) :
    ∃ T1, reachesN (phaseF2 M₀) 4 ⟨.A1 q, T⟩ ⟨.A1 q', T1⟩ ∧
          (∀ j, T1 (Sum.inl j) = Tape.map inlMap (stmt.apply A j)) := by
  classical
  have hproj : projHeads (headsV T) = headsV A := by
    funext i
    have hi : headsV T (Sum.inl i) = Sum.inl ((A i).1) := by
      show (T (Sum.inl i)).1 = _; rw [hwork i, Tape.map_fst]; rfl
    show (match headsV T (Sum.inl i) with | Sum.inl γ => γ | Sum.inr _ => default) = headsV A i
    rw [hi]; rfl
  have hr' : M₀ q (projHeads (headsV T)) = some (q', stmt) := by rw [hproj]; exact hr
  set a := projHeads (headsV T) with ha
  cases stmt with
  | write b' =>
    let TA1 : ι ⊕ Fin 1 → Tape (BennettAlph2 Γ Λ ι) :=
      fun i => match i with
        | Sum.inl j => (T (Sum.inl j)).write (Sum.inl (b' j))
        | Sum.inr k => T (Sum.inr k)
    let TS2 : ι ⊕ Fin 1 → Tape (BennettAlph2 Γ Λ ι) :=
      fun i => match i with
        | Sum.inl j => TA1 (Sum.inl j)
        | Sum.inr _ => (TA1 (Sum.inr 0)).write (Sum.inr (HistEntry2.step q a))
    let T1 : ι ⊕ Fin 1 → Tape (BennettAlph2 Γ Λ ι) :=
      fun i => match i with
        | Sum.inl j => TS2 (Sum.inl j)
        | Sum.inr k => (TS2 (Sum.inr k)).move Dir.right
    refine ⟨T1, ?_, ?_⟩
    · have hTA1blank : (TA1 (Sum.inr 0)).head = (Sum.inl default : BennettAlph2 Γ Λ ι) := hblank
      have r0 : reachesN (phaseF2 M₀) 0 (⟨.A1 q, T⟩ : KCfg _ _ _) ⟨.A1 q, T⟩ := rfl
      exact reachesN_snoc _ (reachesN_snoc _ (reachesN_snoc _
        (reachesN_snoc _ r0 (phaseF2_A1_write M₀ q T hr'))
        (phaseF2_S_write M₀ q a TA1 hr'))
        (phaseF2_step_S2 M₀ q a TA1 hr' hTA1blank))
        (phaseF2_step_C M₀ q' TS2)
    · intro j
      show (T (Sum.inl j)).write (Sum.inl (b' j)) = Tape.map inlMap ((KStmt.write b').apply A j)
      rw [hwork j]; exact (Tape.map_write inlMap (b' j) (A j)).symm
  | move d =>
    let df : ι ⊕ Fin 1 → Option Dir :=
      fun i => match i with | Sum.inl j => d j | Sum.inr _ => none
    let TS : ι ⊕ Fin 1 → Tape (BennettAlph2 Γ Λ ι) := (KStmt.move df).apply T
    let TSd2 : ι ⊕ Fin 1 → Tape (BennettAlph2 Γ Λ ι) :=
      fun i => match i with
        | Sum.inl j => TS (Sum.inl j)
        | Sum.inr _ => (TS (Sum.inr 0)).write (Sum.inr (HistEntry2.step q a))
    let T1 : ι ⊕ Fin 1 → Tape (BennettAlph2 Γ Λ ι) :=
      fun i => match i with
        | Sum.inl j => TSd2 (Sum.inl j)
        | Sum.inr k => (TSd2 (Sum.inr k)).move Dir.right
    refine ⟨T1, ?_, ?_⟩
    · have hTSblank : (TS (Sum.inr 0)).head = (Sum.inl default : BennettAlph2 Γ Λ ι) := by
        show ((KStmt.move df).apply T (Sum.inr 0)).head = _
        simp only [KStmt.apply]; exact hblank
      have r0 : reachesN (phaseF2 M₀) 0 (⟨.A1 q, T⟩ : KCfg _ _ _) ⟨.A1 q, T⟩ := rfl
      exact reachesN_snoc _ (reachesN_snoc _ (reachesN_snoc _
        (reachesN_snoc _ r0 (phaseF2_A1_id M₀ q T hr' (by rintro b ⟨⟩)))
        (phaseF2_S_move M₀ q a T hr'))
        (phaseF2_step_S2 M₀ q a TS hr' hTSblank))
        (phaseF2_step_C M₀ q' TSd2)
    · intro j
      show (KStmt.move df).apply T (Sum.inl j) = Tape.map inlMap ((KStmt.move d).apply A j)
      rcases hd : d j with _ | dir
      · show (match df (Sum.inl j) with | none => _ | some dir => _) = _
        simp only [df, hd]
        show T (Sum.inl j) = Tape.map inlMap ((KStmt.move d).apply A j)
        rw [hwork j]
        show Tape.map inlMap (A j) = _
        simp only [KStmt.apply, hd]
      · show (match df (Sum.inl j) with | none => _ | some dir => _) = _
        simp only [df, hd]
        show (T (Sum.inl j)).move dir = Tape.map inlMap ((KStmt.move d).apply A j)
        rw [hwork j, ← Tape.map_move]
        show Tape.map inlMap ((A j).move dir)
            = Tape.map inlMap (match d j with | none => A j | some dir => (A j).move dir)
        simp only [hd]
  | perm π =>
    let σ : Equiv.Perm (ι ⊕ Fin 1) := Equiv.sumCongr π (Equiv.refl (Fin 1))
    let TS : ι ⊕ Fin 1 → Tape (BennettAlph2 Γ Λ ι) := (KStmt.perm σ).apply T
    let TSd2 : ι ⊕ Fin 1 → Tape (BennettAlph2 Γ Λ ι) :=
      fun i => match i with
        | Sum.inl j => TS (Sum.inl j)
        | Sum.inr _ => (TS (Sum.inr 0)).write (Sum.inr (HistEntry2.step q a))
    let T1 : ι ⊕ Fin 1 → Tape (BennettAlph2 Γ Λ ι) :=
      fun i => match i with
        | Sum.inl j => TSd2 (Sum.inl j)
        | Sum.inr k => (TSd2 (Sum.inr k)).move Dir.right
    refine ⟨T1, ?_, ?_⟩
    · have hTSir : TS (Sum.inr 0) = T (Sum.inr 0) := by
        show T (σ.symm (Sum.inr 0)) = _
        congr 1
      have hTSblank : (TS (Sum.inr 0)).head = (Sum.inl default : BennettAlph2 Γ Λ ι) := by
        rw [hTSir]; exact hblank
      have r0 : reachesN (phaseF2 M₀) 0 (⟨.A1 q, T⟩ : KCfg _ _ _) ⟨.A1 q, T⟩ := rfl
      exact reachesN_snoc _ (reachesN_snoc _ (reachesN_snoc _
        (reachesN_snoc _ r0 (phaseF2_A1_id M₀ q T hr' (by rintro b ⟨⟩)))
        (phaseF2_S_perm M₀ q a T hr'))
        (phaseF2_step_S2 M₀ q a TS hr' hTSblank))
        (phaseF2_step_C M₀ q' TSd2)
    · intro j
      show (KStmt.perm σ).apply T (Sum.inl j) = Tape.map inlMap ((KStmt.perm π).apply A j)
      show T (σ.symm (Sum.inl j)) = Tape.map inlMap (A (π.symm j))
      have hs : σ.symm (Sum.inl j) = Sum.inl (π.symm j) := by
        show (Equiv.sumCongr π (Equiv.refl (Fin 1))).symm (Sum.inl j) = _
        rw [Equiv.sumCongr_symm]; rfl
      rw [hs]; exact hwork (π.symm j)

/-- A counted run embeds into `Reaches`. -/
theorem reachesN_toReaches {M : KMachine Γ Λ ι} :
    ∀ {n : ℕ} {c c' : KCfg Γ Λ ι}, reachesN M n c c' → StateTransition.Reaches (kstep M) c c' := by
  intro n
  induction n with
  | zero => intro c c' h; simp only [reachesN] at h; subst h; exact Relation.ReflTransGen.refl
  | succ n ih =>
    intro c c' h
    simp only [reachesN] at h
    obtain ⟨b, hb, hr⟩ := h
    exact Relation.ReflTransGen.head (Option.mem_def.mpr hb) (ih hr)

/-- **G2-fwd Step 3.**  Forward simulation: if `M₀` runs from `⟨q, A⟩` to a
halting `⟨qf, A'⟩` in `m` steps, and `T` is a `phaseF2` config whose work banks
lift `A` (history head blank, `HistInv`), then `phaseF2` runs from `⟨A1 q, T⟩` to
a halting `⟨A1 qf, T'⟩` whose work banks lift `A'`.  Strong induction on `m`,
peeling one macro at a time. -/
theorem phaseF2_forward_sim (M₀ : KMachine Γ Λ ι) :
    ∀ (m : ℕ) (q : Λ) (A : ι → Tape Γ) (T : ι ⊕ Fin 1 → Tape (BennettAlph2 Γ Λ ι))
      (qf : Λ) (A' : ι → Tape Γ),
      (∀ j, T (Sum.inl j) = Tape.map inlMap (A j)) →
      HistInv ⟨.A1 q, T⟩ →
      reachesN M₀ m ⟨q, A⟩ ⟨qf, A'⟩ → kstep M₀ ⟨qf, A'⟩ = none →
      ∃ T', StateTransition.Reaches (kstep (phaseF2 M₀)) ⟨.A1 q, T⟩ ⟨.A1 qf, T'⟩
        ∧ kstep (phaseF2 M₀) ⟨.A1 qf, T'⟩ = none
        ∧ (∀ j, T' (Sum.inl j) = Tape.map inlMap (A' j)) := by
  classical
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro q A T qf A' hwork hHI hrun hhalt
    have hproj : projHeads (headsV T) = headsV A := by
      funext i
      have hi : headsV T (Sum.inl i) = Sum.inl ((A i).1) := by
        show (T (Sum.inl i)).1 = _; rw [hwork i, Tape.map_fst]; rfl
      show (match headsV T (Sum.inl i) with | Sum.inl γ => γ | Sum.inr _ => default) = headsV A i
      rw [hi]; rfl
    rcases hM : M₀ q (headsV A) with _ | ⟨q', stmt⟩
    · -- M₀ halts immediately at ⟨q, A⟩
      have hkstephalt : kstep (phaseF2 M₀) ⟨.A1 q, T⟩ = none := by
        simp only [kstep, phaseF2, hproj, hM]; rfl
      have hM0halt : kstep M₀ (⟨q, A⟩ : KCfg Γ Λ ι) = none := by
        simp only [kstep, hM]; rfl
      cases m with
      | zero =>
        simp only [reachesN, KCfg.mk.injEq] at hrun
        obtain ⟨rfl, rfl⟩ := hrun
        exact ⟨T, Relation.ReflTransGen.refl, hkstephalt, hwork⟩
      | succ m' =>
        simp only [reachesN] at hrun
        obtain ⟨c1, hc1, _⟩ := hrun
        rw [hM0halt] at hc1; exact absurd hc1 (by simp)
    · -- M₀ steps; peel one macro
      have hM0step : kstep M₀ (⟨q, A⟩ : KCfg Γ Λ ι) = some ⟨q', stmt.apply A⟩ := by
        simp only [kstep, hM, Option.map_some]
      have hm0 : m ≠ 0 := by
        rintro rfl; simp only [reachesN, KCfg.mk.injEq] at hrun
        obtain ⟨rfl, rfl⟩ := hrun
        rw [hM0step] at hhalt; exact absurd hhalt (by simp)
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      simp only [reachesN] at hrun
      obtain ⟨c1, hc1, hrest⟩ := hrun
      rw [hM0step] at hc1
      have heq : c1 = (⟨q', stmt.apply A⟩ : KCfg Γ Λ ι) := (Option.some.inj hc1).symm
      subst heq
      obtain ⟨T1, hfwd4, hwork1⟩ := phaseF2_fwd_macro M₀ A T hwork hHI.2 hM
      have hHI1 : HistInv ⟨.A1 q', T1⟩ := HistInv_reachesN M₀ hfwd4 hHI
      obtain ⟨T', hreach', hhalt', hwork'⟩ :=
        ih m' (by omega) q' (stmt.apply A) T1 qf A' hwork1 hHI1 hrest hhalt
      exact ⟨T', (reachesN_toReaches hfwd4).trans hreach', hhalt', hwork'⟩

/-- **G2-fwd Step 4 (forward correctness, no `sorry`).**  `phaseF2 M₀` computes
`M₀`'s function on the work banks: whenever `M₀` maps `A` to `Y0`, the
descriptor simulator on `liftWork A` halts with an output whose work banks are
the lift of `Y0`.  This is the forward half of `M₀`-faithfulness for `phaseF2`. -/
theorem phaseF2_forward_correct (M₀ : KMachine Γ Λ ι) (q₀ : Λ)
    (A Y0 : ι → Tape Γ) (hY0 : Y0 ∈ ktapeSem M₀ q₀ A) :
    ∃ Y, Y ∈ ktapeSem (phaseF2 M₀) (BennettState2.A1 q₀) (liftWork M₀ A) ∧
         (∀ j, Y (Sum.inl j) = Tape.map inlMap (Y0 j)) := by
  obtain ⟨c, hc, rfl⟩ := (Part.mem_map_iff _).mp hY0
  obtain ⟨hreach, hhalt⟩ := StateTransition.mem_eval.mp hc
  obtain ⟨m, hrun⟩ := reaches_to_reachesN _ hreach
  obtain ⟨qf, Ac⟩ := c
  obtain ⟨T', hreach', hhalt', hwork'⟩ :=
    phaseF2_forward_sim M₀ m q₀ A (liftWork M₀ A) qf Ac (fun j => rfl)
      (HistInv_of_blank_hist (liftWork_blank M₀ A)) hrun hhalt
  exact ⟨T', (Part.mem_map_iff _).mpr
    ⟨⟨.A1 qf, T'⟩, StateTransition.mem_eval.mpr ⟨hreach', hhalt'⟩, rfl⟩, hwork'⟩

end PeriodicTM
