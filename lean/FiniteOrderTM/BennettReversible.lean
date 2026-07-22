/-
FiniteOrderTM/BennettReversible.lean

Track B, milestone M8c' (REOPENED 2026-06-18): the descriptor-encoding
Bennett forward simulator, and the proof that it IS `KReversible`.

BACKGROUND.  The naive phaseF/phaseU simulator in `Reversibilization.lean`
is provably NOT `KReversible` (`phaseF_adv_not_move_uniform`): its forward
phase reads the history tape to choose a move direction.  That negative
result is an artefact of the encoding, not a fundamental obstruction.

THE DESIGN (recover uniformity, then test backdet):
  1. States carry the predecessor `(q, a)` and RECOMPUTE `M₀ q a` to decide
     the move/perm.  So move/perm rules are determined by the STATE, not read
     from the tape → move_uniform / perm_uniform hold.  (A redundant `d`/`π`
     field would create distinct states with identical rules, breaking
     backdet — hence we recompute instead of storing the direction.)
  2. The history descriptor `step q a` (encoding the FULL predecessor) is
     written at the CONVERGENCE step `S2`, just before looping, ONTO a blank
     cell.  Different predecessors write different descriptors.

PHASE F STATE GRAPH (one M₀ step = 4 Bennett steps):

  A1 q  --[write: new work heads, history still blank]-->  S q a
  S q a --[work-op: move d / perm π / no-op move]-->        S2 q a
  S2 q a--[write: descriptor step(q,a) on the blank cell]-->C q'
  C q'  --[move: advance history right]-->                  A1 q'
  (A1 halts -> none when M₀ q a = none.)

OUTCOME (this file, all results no-sorry):
  • `phaseF2_uniformRules`: move/perm uniformity HOLDS.  This REFUTES M8c's
    stated obstruction (that move rules must read the tape).
  • `phaseF2_inv_A1/S/S2/C`: each target state has a unique source shape.
  • `phaseF2_not_backdet`: backdet nonetheless FAILS — for a DEEPER reason
    (the single shared tape alphabet lets history-symbol junk sit on work
    cells, which write rules cannot handle reversibly).  So
    `KReversible (phaseF2 M₀)` is FALSE in this model.
  • `phaseF2_backdet_on_wf`: backdet HOLDS on WELL-FORMED configurations (work
    cells all `Sum.inl`).  So the failure is exactly the junk, and nothing more
    — the simulator is reversible modulo `WFvec`.  This is the common core of
    both genuine fixes (M8d).

CONCLUSION: M8c's verdict (no syntactic `KReversible` Bennett simulator here)
stands, but its REASON is corrected — the obstruction is the shared alphabet,
not the move-direction read — and is now SHARPLY LOCATED: reversibility holds
on well-formed configs (`phaseF2_backdet_on_wf`), so only the junk is missing.
A genuine fix needs per-bank alphabets (`Γ : ι → Type`) or a semantic
reversibility notion (see the closing note).
-/
import FiniteOrderTM.Reversibilization

namespace PeriodicTM

open Turing

variable {Γ : Type*} [Inhabited Γ] [DecidableEq Γ]
variable {Λ : Type*}
variable {ι : Type*}

/-! ### Data types -/

/-- A history-tape symbol recording the FULL predecessor of one M₀ step:
the source state `q` and the head vector `a` it read.  `(q, a)` determines
the whole M₀ transition (via `M₀ q a`), so this is enough to invert the step
and — crucially — to distinguish predecessors at the loop re-entry. -/
inductive HistEntry2 (Γ : Type*) (Λ : Type*) (ι : Type*)
  /-- A recorded step: the source state `q` and the head vector `a` read. -/
  | step (q : Λ) (a : ι → Γ) : HistEntry2 Γ Λ ι

/-- Decidable equality on history entries.  The `step` constructor carries a
function field `a : ι → Γ`, so this is not auto-derivable in general, but with a
finite bank index `ι` (e.g. the single-tape `Unit`) it holds from `DecidableEq`
on `Γ` and `Λ`.  Needed so the full-string copy leg (`copyStr`, which branches on
`= default`) can run at the wrapper alphabet `BennettAlph2`. -/
instance instDecidableEqHistEntry2 {Γ Λ ι : Type*}
    [Fintype ι] [DecidableEq Γ] [DecidableEq Λ] :
    DecidableEq (HistEntry2 Γ Λ ι) := by
  intro x y
  cases x with
  | step q a =>
    cases y with
    | step q' a' => exact decidable_of_iff (q = q' ∧ a = a') (by rw [HistEntry2.step.injEq])

/-- Tape alphabet of the descriptor-encoding Bennett machine.  The blank is
`Sum.inl default` (the work-side blank), so EVERY work cell is always a
`Sum.inl _` value — its raw form is fully recovered from its projection, which
`backdet` needs when a write rule overwrites it.  The history cell is blank
(`Sum.inl default`) or a recorded step (`Sum.inr _`); telling them apart at the
descriptor write needs `[DecidableEq Γ]` (decidable equality to the blank). -/
abbrev BennettAlph2 (Γ : Type*) (Λ : Type*) (ι : Type*) := Γ ⊕ HistEntry2 Γ Λ ι

instance instInhabitedBennettAlph2 [Inhabited Γ] :
    Inhabited (BennettAlph2 Γ Λ ι) :=
  ⟨Sum.inl default⟩

/-- State of the descriptor-encoding Bennett machine (phase F only, for now).
States carry the predecessor `(q, a)`; the rule is recomputed from `M₀ q a`,
so move/perm rules are head-uniform without storing the direction. -/
inductive BennettState2 (Γ : Type*) (Λ : Type*) (ι : Type*)
  | A1 (q : Λ)                : BennettState2 Γ Λ ι
  | S  (q : Λ) (a : ι → Γ)    : BennettState2 Γ Λ ι
  | S2 (q : Λ) (a : ι → Γ)    : BennettState2 Γ Λ ι
  | C  (q' : Λ)               : BennettState2 Γ Λ ι

/-! ### The forward simulator -/

/-- Project the work-bank heads (the `Γ` component) from a Bennett head vector.
Named (rather than inlined) so that single-step lemmas about `phaseF2`'s `A1`
rule can rewrite `M₀ q (projHeads b)` -- an inline `match` would compile to a
private matcher that neither `simp` nor `rw` can target. -/
def projHeads (b : ι ⊕ Fin 1 → BennettAlph2 Γ Λ ι) : ι → Γ :=
  fun i => match b (Sum.inl i) with
    | .inl γ => γ
    | .inr _ => default

/-- Phase F of the descriptor-encoding Bennett machine. -/
noncomputable def phaseF2 (M₀ : KMachine Γ Λ ι) :
    KMachine (BennettAlph2 Γ Λ ι) (BennettState2 Γ Λ ι) (ι ⊕ Fin 1) :=
  fun s b =>
  match s with
  | .A1 q =>
    -- read the work heads (project the left component)
    let a : ι → Γ := projHeads b
    match M₀ q a with
    | none => none
    | some (_, KStmt.write b') =>
      -- write the new work heads; history cell stays blank; carry (q, a)
      some (.S q a, KStmt.write (fun i => match i with
        | Sum.inl j => Sum.inl (b' j)
        | Sum.inr k => b (Sum.inr k)))
    | some (_, KStmt.move _) =>
      -- work unchanged (identity write); carry (q, a)
      some (.S q a, KStmt.write b)
    | some (_, KStmt.perm _) =>
      some (.S q a, KStmt.write b)
  | .S q a =>
    -- recompute M₀ q a; perform the work-op (direction/perm from the state)
    match M₀ q a with
    | none => none
    | some (_, KStmt.write _) =>
      -- write already applied at A1; advance nothing (no-op move)
      some (.S2 q a, KStmt.move (fun _ => none))
    | some (_, KStmt.move d) =>
      some (.S2 q a, KStmt.move (fun i => match i with
        | Sum.inl j => d j
        | Sum.inr _ => none))
    | some (_, KStmt.perm π) =>
      some (.S2 q a, KStmt.perm (Equiv.sumCongr π (Equiv.refl _)))
  | .S2 q a =>
    -- write the descriptor step(q,a) — but ONLY onto a BLANK history cell.  The
    -- write blank↦step is then injective (the flip recovers the old blank),
    -- which is exactly what `backdet` needs at the loop re-entry C.
    match M₀ q a with
    | none => none
    | some (q', _) =>
      match b (Sum.inr (0 : Fin 1)) with
      | Sum.inl x =>
        if x = default then
          some (.C q', KStmt.write (fun i => match i with
            | Sum.inl j => b (Sum.inl j)
            | Sum.inr _ => Sum.inr (HistEntry2.step q a)))
        else none
      | Sum.inr _ => none
  | .C q' =>
    -- advance the history head right; work stays put
    some (.A1 q', KStmt.move (fun i => match i with
      | Sum.inl _ => none
      | Sum.inr _ => some Dir.right))

/-! ### Uniformity (the conditions the naive encoding failed) -/

/-- Move rules of `phaseF2` are head-uniform: the move-producing states `S`
(write/move cases) and `C` recompute their rule from the state, ignoring the
head vector. -/
theorem phaseF2_move_uniform (M₀ : KMachine Γ Λ ι) :
    ∀ {p a q d}, phaseF2 M₀ p a = some (q, KStmt.move d) →
    ∀ a', phaseF2 M₀ p a' = some (q, KStmt.move d) := by
  intro p a q d h a'
  cases p with
  | A1 q0 => simp only [phaseF2] at h; (repeat' split at h) <;> simp_all
  | S q0 a0 => exact h
  | S2 q0 a0 => simp only [phaseF2] at h; (repeat' split at h) <;> simp_all
  | C q0 => exact h

/-- Perm rules of `phaseF2` are head-uniform: only `S` (perm case) produces a
perm rule, recomputed from the state. -/
theorem phaseF2_perm_uniform (M₀ : KMachine Γ Λ ι) :
    ∀ {p a q π}, phaseF2 M₀ p a = some (q, KStmt.perm π) →
    ∀ a', phaseF2 M₀ p a' = some (q, KStmt.perm π) := by
  intro p a q π h a'
  cases p with
  | A1 q0 => simp only [phaseF2] at h; (repeat' split at h) <;> simp_all
  | S q0 a0 => exact h
  | S2 q0 a0 => simp only [phaseF2] at h; (repeat' split at h) <;> simp_all
  | C q0 => simp [phaseF2] at h

/-- `phaseF2` satisfies the uniformity half of `KReversible`. -/
theorem phaseF2_uniformRules (M₀ : KMachine Γ Λ ι) :
    UniformRules (phaseF2 M₀) :=
  ⟨phaseF2_move_uniform M₀, phaseF2_perm_uniform M₀⟩

/-! ### Toward backdet: target-state inversions

Each target state of `phaseF2` is produced by a UNIQUE source-state shape.
These four lemmas establish that (the structural core of backward
determinism): the state graph has no spurious convergences.  Combined with
the descriptor argument at `C` (below), they give `backdet`. -/

/-- Only `C q0'` (the history-advance move) produces target `A1 q0'`. -/
theorem phaseF2_inv_A1 (M₀ : KMachine Γ Λ ι) {p a q0' st}
    (h : phaseF2 M₀ p a = some (.A1 q0', st)) : p = .C q0' := by
  cases p with
  | A1 q0 => simp only [phaseF2] at h; (repeat' split at h) <;> simp_all
  | S q0 a0 => simp only [phaseF2] at h; (repeat' split at h) <;> simp_all
  | S2 q0 a0 => simp only [phaseF2] at h; (repeat' split at h) <;> simp_all
  | C q0 => simp only [phaseF2] at h; simp_all

/-- Only `A1 q0` (the dispatch write) produces target `S q0 a0`. -/
theorem phaseF2_inv_S (M₀ : KMachine Γ Λ ι) {p a q0 a0 st}
    (h : phaseF2 M₀ p a = some (.S q0 a0, st)) : p = .A1 q0 := by
  cases p with
  | A1 q1 => simp only [phaseF2] at h; (repeat' split at h) <;> simp_all
  | S q1 a1 => simp only [phaseF2] at h; (repeat' split at h) <;> simp_all
  | S2 q1 a1 => simp only [phaseF2] at h; (repeat' split at h) <;> simp_all
  | C q1 => simp only [phaseF2] at h; simp_all

/-- Only `S q0 a0` (the work-op) produces target `S2 q0 a0`. -/
theorem phaseF2_inv_S2 (M₀ : KMachine Γ Λ ι) {p a q0 a0 st}
    (h : phaseF2 M₀ p a = some (.S2 q0 a0, st)) : p = .S q0 a0 := by
  cases p with
  | A1 q1 => simp only [phaseF2] at h; (repeat' split at h) <;> simp_all
  | S q1 a1 => simp only [phaseF2] at h; (repeat' split at h) <;> simp_all
  | S2 q1 a1 => simp only [phaseF2] at h; (repeat' split at h) <;> simp_all
  | C q1 => simp only [phaseF2] at h; simp_all

/-- Only `S2 q0 a0` (the descriptor write) produces target `C q0'`. -/
theorem phaseF2_inv_C (M₀ : KMachine Γ Λ ι) {p a q0' st}
    (h : phaseF2 M₀ p a = some (.C q0', st)) : ∃ q0 a0, p = .S2 q0 a0 := by
  cases p with
  | A1 q1 => simp only [phaseF2] at h; (repeat' split at h) <;> simp_all
  | S q1 a1 => simp only [phaseF2] at h; (repeat' split at h) <;> simp_all
  | S2 q1 a1 => exact ⟨q1, a1, rfl⟩
  | C q1 => simp only [phaseF2] at h; simp_all

/-! ### backdet FAILS — a second, deeper obstruction (the decisive finding)

The four inversions handle the *source-shape* half of backward determinism:
each target state has a unique source shape.  But that is NOT enough, and in
fact `backdet` is FALSE for `phaseF2` — for a reason quite different from the
one M8c reported (move rules reading the tape, which the descriptor encoding
DID fix).

The new obstruction is the SHARED TAPE ALPHABET.  Every bank (work and
history) uses `BennettAlph2 = Γ ⊕ HistEntry2`, so a work cell can hold a
`Sum.inr` "history symbol" as junk.  Such configurations are unreachable, but
the *syntactic* `backdet` quantifies over all head vectors.  When M₀'s rule is
a write, `A1`'s rule overwrites the work cell and records only the PROJECTED
old heads (`ι → Γ`) — it discards the raw `Sum.inr` junk.  Hence two reads that
differ only in junk produce the SAME written vector, giving two demands at one
slot with different recorded reads: `backdet` is violated.

`phaseF2_not_backdet` below is a FORMAL witness of this (no sorry): for any M₀
with a write rule at `(q0, blank)`, the clean read and a junk read collide. -/

/-- **`phaseF2` is not backward-deterministic.**  Given a write rule of M₀, a
work cell carrying a junk history symbol is indistinguishable from a blank to
the simulator, yet records a different read — refuting `backdet`.  (Needs
`[DecidableEq ι]` only to build the one-cell-perturbed read via
`Function.update`.) -/
theorem phaseF2_not_backdet [DecidableEq ι] (M₀ : KMachine Γ Λ ι)
    (i0 : ι) {q0 q0' : Λ} {b' : ι → Γ}
    (hw : M₀ q0 (fun _ => default) = some (q0', KStmt.write b')) :
    ¬ (∀ {q : BennettState2 Γ Λ ι} {b v₁ v₂},
        Demand (phaseF2 M₀) q b v₁ → Demand (phaseF2 M₀) q b v₂ → v₁ = v₂) := by
  intro hbd
  let ac : (ι ⊕ Fin 1) → BennettAlph2 Γ Λ ι := fun _ => Sum.inl default
  let aj : (ι ⊕ Fin 1) → BennettAlph2 Γ Λ ι :=
    Function.update ac (Sum.inl i0) (Sum.inr (HistEntry2.step q0 (fun _ => default)))
  let Wt : (ι ⊕ Fin 1) → BennettAlph2 Γ Λ ι := fun i => match i with
    | Sum.inl j => Sum.inl (b' j) | Sum.inr _ => Sum.inl default
  have rc : phaseF2 M₀ (.A1 q0) ac = some (.S q0 (fun _ => default), KStmt.write Wt) := by
    show (match M₀ q0 (fun _ : ι => default) with
      | none => none
      | some (_, KStmt.write bb) =>
          some (BennettState2.S q0 (fun _ => default), KStmt.write (fun i => match i with
            | Sum.inl j => Sum.inl (bb j) | Sum.inr k => ac (Sum.inr k)))
      | some (_, KStmt.move _) => some (BennettState2.S q0 (fun _ => default), KStmt.write ac)
      | some (_, KStmt.perm _) => some (BennettState2.S q0 (fun _ => default), KStmt.write ac)) = _
    rw [hw]
    rfl
  have paj : (fun i => match aj (Sum.inl i) with | Sum.inl γ => γ | Sum.inr _ => default)
      = (fun _ : ι => default) := by
    funext i; by_cases hi : i = i0
    · subst hi; simp only [aj, Function.update_self]
    · rw [show aj (Sum.inl i) = ac (Sum.inl i) from
        Function.update_of_ne (by simp [hi]) _ _]
  have rj : phaseF2 M₀ (.A1 q0) aj = some (.S q0 (fun _ => default), KStmt.write Wt) := by
    have key : phaseF2 M₀ (.A1 q0) aj =
      (match M₀ q0 (fun i : ι => match aj (Sum.inl i) with
              | Sum.inl γ => γ | Sum.inr _ => default) with
        | none => none
        | some (_, KStmt.write bb) =>
            some (BennettState2.S q0 (fun i => match aj (Sum.inl i) with
                    | Sum.inl γ => γ | Sum.inr _ => default),
              KStmt.write (fun i => match i with
                | Sum.inl j => Sum.inl (bb j) | Sum.inr k => aj (Sum.inr k)))
        | some (_, KStmt.move _) => some (BennettState2.S q0 (fun i => match aj (Sum.inl i) with
                    | Sum.inl γ => γ | Sum.inr _ => default), KStmt.write aj)
        | some (_, KStmt.perm _) => some (BennettState2.S q0 (fun i => match aj (Sum.inl i) with
                    | Sum.inl γ => γ | Sum.inr _ => default), KStmt.write aj)) := rfl
    rw [key, paj, hw]
    have hP : (fun i : ι ⊕ Fin 1 => match i with
        | Sum.inl j => Sum.inl (b' j) | Sum.inr k => aj (Sum.inr k)) = Wt := by
      funext i; rcases i with j | k
      · rfl
      · exact Function.update_of_ne (by simp) _ _
    show some (BennettState2.S q0 (fun _ => default),
        KStmt.write (fun i => match i with
          | Sum.inl j => Sum.inl (b' j) | Sum.inr k => aj (Sum.inr k)))
      = some (BennettState2.S q0 (fun _ => default), KStmt.write Wt)
    rw [hP]
  have e := hbd (Demand.write rc) (Demand.write rj)
  rw [Prod.mk.injEq] at e
  have hace : ac = aj := by injection e.2
  have hcontra := congrFun hace (Sum.inl i0)
  rw [show aj (Sum.inl i0) = Sum.inr (HistEntry2.step q0 (fun _ : ι => default)) from
    Function.update_self _ _ _] at hcontra
  exact absurd hcontra (by simp [ac])

/-! ### WF-restricted backward determinism (the approach-agnostic core, M8d)

`backdet` fails only on UNREACHABLE configurations carrying work-tape junk.
Restricted to WELL-FORMED head vectors — every work cell is a `Sum.inl` — the
simulator IS backward-deterministic.  `phaseF2_backdet_on_wf` proves this
(no sorry).  It is the common core of both genuine fixes: per-bank alphabets
make well-formedness automatic, and semantic reversibility quantifies over the
reachable (hence well-formed) configurations.  So the simulator is "morally"
reversible; only the shared-alphabet junk blocks the unconditional syntactic
statement. -/

/-- A head vector is well-formed if every work cell holds a `Sum.inl` value
(no history-symbol junk on the work banks). -/
def WFvec (a : (ι ⊕ Fin 1) → BennettAlph2 Γ Λ ι) : Prop :=
  ∀ j : ι, ∃ γ, a (Sum.inl j) = Sum.inl γ

/-- Under well-formedness, `A1`'s write rule recovers its read from the target
state `a0` and the written vector `b`. -/
theorem phaseF2_A1_recover (M₀ : KMachine Γ Λ ι) {q0 : Λ} {a0 : ι → Γ}
    {b a : (ι ⊕ Fin 1) → BennettAlph2 Γ Λ ι}
    (h : phaseF2 M₀ (.A1 q0) a = some (.S q0 a0, KStmt.write b)) (w : WFvec a) :
    a = (fun i => match i with | Sum.inl j => Sum.inl (a0 j) | Sum.inr k => b (Sum.inr k)) := by
  have hproj : (fun j => match a (Sum.inl j) with | Sum.inl γ => γ | Sum.inr _ => default) = a0 := by
    simp only [phaseF2] at h
    split at h
    · exact absurd h (by simp)
    · rw [Option.some.injEq, Prod.ext_iff, BennettState2.S.injEq] at h; exact h.1.2
    · rw [Option.some.injEq, Prod.ext_iff, BennettState2.S.injEq] at h; exact h.1.2
    · rw [Option.some.injEq, Prod.ext_iff, BennettState2.S.injEq] at h; exact h.1.2
  have hhist : ∀ k, a (Sum.inr k) = b (Sum.inr k) := by
    intro k
    simp only [phaseF2] at h
    split at h
    · exact absurd h (by simp)
    · rw [Option.some.injEq, Prod.ext_iff] at h
      injection h.2 with hwb; have := congrFun hwb (Sum.inr k); simpa using this
    · rw [Option.some.injEq, Prod.ext_iff] at h
      injection h.2 with hwb; have := congrFun hwb (Sum.inr k); simpa using this
    · rw [Option.some.injEq, Prod.ext_iff] at h
      injection h.2 with hwb; have := congrFun hwb (Sum.inr k); simpa using this
  funext i
  cases i with
  | inl j =>
    obtain ⟨γ, hγ⟩ := w j
    have hp := congrFun hproj j
    rw [hγ] at hp ⊢; simp only at hp ⊢; rw [hp]
  | inr k => exact hhist k

/-- `S2`'s descriptor-write recovers its read from `b`, and the descriptor on
`b` pins down the source `(qx, ax)`.  (No well-formedness needed: the
blank-check pins the history cell, the work cells are copied verbatim.) -/
theorem phaseF2_S2_recover (M₀ : KMachine Γ Λ ι) {qx : Λ} {ax : ι → Γ}
    {q' : Λ} {a b : (ι ⊕ Fin 1) → BennettAlph2 Γ Λ ι}
    (h : phaseF2 M₀ (.S2 qx ax) a = some (.C q', KStmt.write b)) :
    a = (fun i => match i with | Sum.inl j => b (Sum.inl j) | Sum.inr _ => Sum.inl default)
    ∧ b (Sum.inr (0:Fin 1)) = Sum.inr (HistEntry2.step qx ax) := by
  simp only [phaseF2] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · rename_i x hx
      split at h
      · rename_i hxd
        rw [Option.some.injEq, Prod.ext_iff] at h
        injection h.2 with hb
        refine ⟨?_, ?_⟩
        · funext i; cases i with
          | inl j => simpa using congrFun hb (Sum.inl j)
          | inr k => have hk : k = 0 := Subsingleton.elim _ _
                     subst hk; rw [hx, hxd]
        · simpa using (congrFun hb (Sum.inr (0:Fin 1))).symm
      · exact absurd h (by simp)
    · exact absurd h (by simp)

/-- A write rule and a move rule cannot share a target state. -/
theorem phaseF2_no_write_move (M₀ : KMachine Γ Λ ι) {p₁ a₁ p₂ a₂ q bb dd}
    (h₁ : phaseF2 M₀ p₁ a₁ = some (q, KStmt.write bb))
    (h₂ : phaseF2 M₀ p₂ a₂ = some (q, KStmt.move dd)) : False := by
  cases q with
  | A1 q' => have e := phaseF2_inv_A1 M₀ h₁; subst e; simp [phaseF2] at h₁
  | S q0 a0 => have e := phaseF2_inv_S M₀ h₂; subst e
               simp only [phaseF2] at h₂; (repeat' split at h₂) <;> simp_all
  | S2 q0 a0 => have e := phaseF2_inv_S2 M₀ h₁; subst e
                simp only [phaseF2] at h₁; (repeat' split at h₁) <;> simp_all
  | C q' => obtain ⟨qx, ax, e⟩ := phaseF2_inv_C M₀ h₂; subst e
            simp only [phaseF2] at h₂; (repeat' split at h₂) <;> simp_all

/-- A write rule and a perm rule cannot share a target state. -/
theorem phaseF2_no_write_perm (M₀ : KMachine Γ Λ ι) {p₁ a₁ p₂ a₂ q bb pp}
    (h₁ : phaseF2 M₀ p₁ a₁ = some (q, KStmt.write bb))
    (h₂ : phaseF2 M₀ p₂ a₂ = some (q, KStmt.perm pp)) : False := by
  cases q with
  | A1 q' => have e := phaseF2_inv_A1 M₀ h₁; subst e; simp [phaseF2] at h₁
  | S q0 a0 => have e := phaseF2_inv_S M₀ h₂; subst e
               simp only [phaseF2] at h₂; (repeat' split at h₂) <;> simp_all
  | S2 q0 a0 => have e := phaseF2_inv_S2 M₀ h₁; subst e
                simp only [phaseF2] at h₁; (repeat' split at h₁) <;> simp_all
  | C q' => obtain ⟨qx, ax, e⟩ := phaseF2_inv_C M₀ h₂; subst e
            simp only [phaseF2] at h₂; (repeat' split at h₂) <;> simp_all

/-- A move rule and a perm rule cannot share a target state. -/
theorem phaseF2_no_move_perm (M₀ : KMachine Γ Λ ι) {p₁ a₁ p₂ a₂ q dd pp}
    (h₁ : phaseF2 M₀ p₁ a₁ = some (q, KStmt.move dd))
    (h₂ : phaseF2 M₀ p₂ a₂ = some (q, KStmt.perm pp)) : False := by
  cases q with
  | A1 q' => have e := phaseF2_inv_A1 M₀ h₂; subst e; simp [phaseF2] at h₂
  | S q0 a0 => have e := phaseF2_inv_S M₀ h₁; subst e
               simp only [phaseF2] at h₁; (repeat' split at h₁) <;> simp_all
  | S2 q0 a0 => have e1 := phaseF2_inv_S2 M₀ h₁; have e2 := phaseF2_inv_S2 M₀ h₂
                subst e1; rw [e2] at h₂
                have hco : phaseF2 M₀ (.S q0 a0) a₁ = phaseF2 M₀ (.S q0 a0) a₂ := rfl
                rw [h₁, h₂] at hco; simp at hco
  | C q' => obtain ⟨qx, ax, e⟩ := phaseF2_inv_C M₀ h₁; subst e
            simp only [phaseF2] at h₁; (repeat' split at h₁) <;> simp_all

/-- **Backward determinism on well-formed configurations.**  If two demands at
the same slot have well-formed recorded reads, they agree.  The descriptor
encoding is therefore reversible exactly modulo the shared-alphabet junk that
`WFvec` rules out — the precise sense in which the construction is correct. -/
theorem phaseF2_backdet_on_wf (M₀ : KMachine Γ Λ ι)
    {q : BennettState2 Γ Λ ι} {b v₁ v₂}
    (d₁ : Demand (phaseF2 M₀) q b v₁) (d₂ : Demand (phaseF2 M₀) q b v₂)
    (w₁ : ∀ a, v₁.2 = KStmt.write a → WFvec a)
    (w₂ : ∀ a, v₂.2 = KStmt.write a → WFvec a) : v₁ = v₂ := by
  cases d₁ with
  | write hr₁ =>
    rename_i p₁ a₁
    have wa1 : WFvec a₁ := w₁ a₁ rfl
    cases d₂ with
    | write hr₂ =>
      rename_i p₂ a₂
      have wa2 : WFvec a₂ := w₂ a₂ rfl
      cases q with
      | A1 q' => have e := phaseF2_inv_A1 M₀ hr₁; subst e; simp [phaseF2] at hr₁
      | S q0 a0 =>
        have e1 := phaseF2_inv_S M₀ hr₁; have e2 := phaseF2_inv_S M₀ hr₂
        subst e1; subst e2
        rw [phaseF2_A1_recover M₀ hr₁ wa1, phaseF2_A1_recover M₀ hr₂ wa2]
      | S2 q0 a0 => have e := phaseF2_inv_S2 M₀ hr₁; subst e
                    simp only [phaseF2] at hr₁; (repeat' split at hr₁) <;> simp_all
      | C q' =>
        obtain ⟨qx, ax, e1⟩ := phaseF2_inv_C M₀ hr₁
        obtain ⟨qy, ay, e2⟩ := phaseF2_inv_C M₀ hr₂
        subst e1; subst e2
        obtain ⟨ra1, rb1⟩ := phaseF2_S2_recover M₀ hr₁
        obtain ⟨ra2, rb2⟩ := phaseF2_S2_recover M₀ hr₂
        have hs := rb1.symm.trans rb2
        simp only [Sum.inr.injEq, HistEntry2.step.injEq] at hs
        obtain ⟨hq, ha⟩ := hs; subst hq; subst ha
        rw [ra1, ra2]
    | move _ hr₂ => exact (phaseF2_no_write_move M₀ hr₁ hr₂).elim
    | perm _ hr₂ => exact (phaseF2_no_write_perm M₀ hr₁ hr₂).elim
  | move _ hr₁ =>
    rename_i p₁ a₁ dd₁
    cases d₂ with
    | write hr₂ => exact (phaseF2_no_write_move M₀ hr₂ hr₁).elim
    | move _ hr₂ =>
      rename_i p₂ a₂ dd₂
      cases q with
      | A1 q' =>
        have e1 := phaseF2_inv_A1 M₀ hr₁; have e2 := phaseF2_inv_A1 M₀ hr₂
        subst e1; subst e2
        have hco : phaseF2 M₀ (.C q') a₁ = phaseF2 M₀ (.C q') a₂ := rfl
        rw [hr₁, hr₂] at hco
        simp only [Option.some.injEq, Prod.mk.injEq, KStmt.move.injEq] at hco
        rw [hco.2]
      | S q0 a0 => have e := phaseF2_inv_S M₀ hr₁; subst e
                   simp only [phaseF2] at hr₁; (repeat' split at hr₁) <;> simp_all
      | S2 q0 a0 =>
        have e1 := phaseF2_inv_S2 M₀ hr₁; have e2 := phaseF2_inv_S2 M₀ hr₂
        subst e1; subst e2
        have hco : phaseF2 M₀ (.S q0 a0) a₁ = phaseF2 M₀ (.S q0 a0) a₂ := rfl
        rw [hr₁, hr₂] at hco
        simp only [Option.some.injEq, Prod.mk.injEq, KStmt.move.injEq] at hco
        rw [hco.2]
      | C q' => obtain ⟨qx, ax, e⟩ := phaseF2_inv_C M₀ hr₁; subst e
                simp only [phaseF2] at hr₁; (repeat' split at hr₁) <;> simp_all
    | perm _ hr₂ => exact (phaseF2_no_move_perm M₀ hr₁ hr₂).elim
  | perm _ hr₁ =>
    rename_i p₁ a₁ pp₁
    cases d₂ with
    | write hr₂ => exact (phaseF2_no_write_perm M₀ hr₂ hr₁).elim
    | move _ hr₂ => exact (phaseF2_no_move_perm M₀ hr₂ hr₁).elim
    | perm _ hr₂ =>
      rename_i p₂ a₂ pp₂
      cases q with
      | A1 q' => have e := phaseF2_inv_A1 M₀ hr₁; subst e; simp [phaseF2] at hr₁
      | S q0 a0 => have e := phaseF2_inv_S M₀ hr₁; subst e
                   simp only [phaseF2] at hr₁; (repeat' split at hr₁) <;> simp_all
      | S2 q0 a0 =>
        have e1 := phaseF2_inv_S2 M₀ hr₁; have e2 := phaseF2_inv_S2 M₀ hr₂
        subst e1; subst e2
        have hco : phaseF2 M₀ (.S q0 a0) a₁ = phaseF2 M₀ (.S q0 a0) a₂ := rfl
        rw [hr₁, hr₂] at hco
        simp only [Option.some.injEq, Prod.mk.injEq, KStmt.perm.injEq] at hco
        rw [hco.2]
      | C q' => obtain ⟨qx, ax, e⟩ := phaseF2_inv_C M₀ hr₁; subst e
                simp only [phaseF2] at hr₁; (repeat' split at hr₁) <;> simp_all

/-
WHAT THIS MEANS FOR M8.

The descriptor encoding genuinely fixed M8c's stated obstruction
(`phaseF2_uniformRules` — move/perm rules need not read the tape).  But a
syntactically `KReversible` Bennett simulator is still out of reach IN THIS
MODEL, now for a sharper reason: the single shared tape alphabet across all
banks.  Two ways forward, both real model changes (out of scope here):

  • PER-BANK ALPHABETS.  Generalise `KMachine` to an index-dependent alphabet
    `Γ : ι → Type`.  Then work cells have type `Γ work` with no history
    symbols, the projection is faithful, the junk vanishes, and backdet should
    go through via the four inversions + descriptor injectivity at C.

  • SEMANTIC REVERSIBILITY.  Replace syntactic `KReversible` by a behavioural
    bijection on REACHABLE configurations (where work cells are always
    `Sum.inl _`), and re-derive the flip/symmetrisation layer (M5–M7) under it.

So M8c's *conclusion* (no syntactic `KReversible` for Bennett in this model)
stands, but its *reason* is corrected and deepened: not the move-direction
read (fixable), but the shared-alphabet work-tape junk (needs a new model).
And `phaseF2_backdet_on_wf` pins the gap exactly: reversibility already holds
on well-formed configs, so either model change above closes it by making
well-formedness hold of every configuration in scope.
-/

end PeriodicTM
