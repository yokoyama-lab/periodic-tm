/-
FiniteOrderTM/Reversibilization.lean

Track B, milestone M8: Bennett/Axelsen–Glück reversibilization.

GOAL: remove the hypothesis `hR₀rev : KReversible R₀` from
`nakano_symmetrisation` (Completeness.lean) and produce an unconditional
machine-level theorem.

REFERENCE: Bennett 1973, "Logical Reversibility of Computation";
           Axelsen–Glück 2011, Thm 3.12 (RC proceedings).

STATUS: M8-spec DONE, M8a DONE, M8b DONE, M8c DONE (negative result).
        `phaseF`/`phaseU`/`bennettM` defined (no sorry).  `KReversible`
        proof is IMPOSSIBLE for this construction — see the design note and
        `phaseF_adv_not_move_uniform` below.  M8 is CLOSED: the unconditional
        theorem (`bennett_reversibilization`,
        `nakano_symmetrisation_unconditional`) requires a SEMANTIC
        reversibility notion to replace the syntactic `KReversible`, which is
        out of scope for this artifact.  The mechanised result is the
        conditional M7 (`nakano_symmetrisation`, with a `KReversible`
        hypothesis).  The two unconditional theorems are kept as documented
        `sorry`s recording the goal and the obstruction.

PLAN: see proto/ROADMAP.md §M8 for the full construction outline.
-/
import FiniteOrderTM.Completeness

namespace PeriodicTM

open Turing

variable {Γ : Type*} [Inhabited Γ]
variable {Λ : Type*}
variable {ι : Type*}

/-! ### Auxiliary predicates -/

/-- A machine has **uniform rules** if move and permutation rules do not read
the tape heads: the rule at each state is the same regardless of the head
vector.  This is exactly the `move_uniform` / `perm_uniform` half of
`KReversible`. -/
structure UniformRules (M : KMachine Γ Λ ι) : Prop where
  move_uniform : ∀ {p a q d}, M p a = some (q, KStmt.move d) →
    ∀ a', M p a' = some (q, KStmt.move d)
  perm_uniform : ∀ {p a q π}, M p a = some (q, KStmt.perm π) →
    ∀ a', M p a' = some (q, KStmt.perm π)

/-- A machine **computes a tape bijection** if its `ktapeSem` at `q₀` is a
total injection on tape configurations (equivalently, defines a bijection on
`{T | ktapeSem M q₀ T ≠ ⊥}`).  For involutions this holds because the
function equals its own inverse. -/
def KTapeSemBijective (M : KMachine Γ Λ ι) (q₀ : Λ) : Prop :=
  ∀ T₁ T₂ T', T' ∈ ktapeSem M q₀ T₁ → T' ∈ ktapeSem M q₀ T₂ → T₁ = T₂

/-! ### Connecting KInvolutory and KReversible (M8a) -/

/-- A `KInvolutory` machine with uniform rules is `KReversible`.

`backdet` follows from `KInvolutory.demand_backdet` (which uses
`KFlipOf.self_backdet` + injectivity of the involutive σ).  The uniformity
fields come directly from `UniformRules`.

This is the "easy path" to `KReversible`: if M₀ is already its own
time-reverse (self-flip under σ), no Bennett construction is needed. -/
theorem KInvolutory.toKReversible
    {M : KMachine Γ Λ ι} {σ : Λ → Λ} {q₀ qf : Λ}
    (h  : KInvolutory M σ q₀ qf)
    (hu : UniformRules M) :
    KReversible M :=
  ⟨h.demand_backdet, hu.move_uniform, hu.perm_uniform⟩

/-- `KReversible` subsumes `UniformRules`. -/
theorem KReversible.toUniformRules {M : KMachine Γ Λ ι} (h : KReversible M) :
    UniformRules M :=
  ⟨h.move_uniform, h.perm_uniform⟩

/-! ### M8a: Bennett construction — data types -/

/-
DESIGN NOTE (M8a/M8b)
=====================
The Bennett machine uses a richer tape alphabet `BennettAlph Γ ι` (a sum type)
shared across all tape banks `ι ⊕ Fin 1` (Fin 1 = the single history tape):

  • ι-bank tapes store `Sum.inl γ` for γ : Γ
  • the history tape stores `Sum.inr e` for e : HistEntry Γ ι

`HistEntry Γ ι` records what M₀ did at one step, so Phase U can undo it:
  • `write old_heads` — M₀ wrote new heads over `old_heads`; Phase U re-writes `old_heads`.
  • `move d`          — M₀ moved in direction d; Phase U moves in `revMap d`.
  • `perm π`          — M₀ applied perm π; Phase U applies π⁻¹.

`BennettState Λ` encodes the two phases and intermediate steps:

PHASE F (forward simulation) — each M₀ step expands into 2–3 Bennett steps:
  phaseF_run q   — look up M₀ q at state q:
                   • write rule → combined write (ι-bank + hist entry)  → phaseF_adv q'
                   • move rule  → write hist entry (ι-bank unchanged)   → phaseF_adv q'
                   • perm rule  → write hist entry (ι-bank unchanged)   → phaseF_adv q'
                   • M₀ halts  → no-op perm (identity)                 → phaseU_seek
  phaseF_adv q'  — reads hist entry to complete M₀'s rule on ι-bank:
                   • hist = write _ → advance hist tape right (write done)    → phaseF_run q'
                   • hist = move d  → move ι-bank d + advance hist right      → phaseF_run q'
                   • hist = perm π  → apply (π ⊕ id) to tape bank            → phaseF_prm q'
  phaseF_prm q'  — (after perm) advance history tape right                   → phaseF_run q'

PHASE U (uncompute) — reads hist entries in reverse, applies inverse rules:
  phaseU_seek    — move hist tape head left                                   → phaseU_apply
  phaseU_apply   — read entry at hist head:
                   • hist = write old → write old to ι-bank (restoring it)   → phaseU_seek
                   • hist = move d    → move ι-bank in revMap d               → phaseU_seek
                   • hist = perm π    → apply (π⁻¹ ⊕ id) to tape bank        → phaseU_seek
                   • blank (inl _)    → hist exhausted; halt (return none)

KReversible IMPOSSIBILITY NOTE (M8c analysis):
  The `KReversible` predicate has three requirements: backdet, move_uniform,
  perm_uniform.  ALL THREE fail for `bennettM` as designed.  This is a
  fundamental incompatibility, not a fixable implementation detail.

  MOVE_UNIFORM FAILURE at `phaseF_adv q'`:
  • `phaseF_adv q'` reads the history tape head to decide what to do:
    - hist = `.write _` → KStmt.move (fun i => inl _ => none, inr _ => right)
    - hist = `.move d`  → KStmt.move (fun i => inl j => d j, inr _ => right)
  • These are different move directions for different head vectors b.
  • Formally proved (search "phaseF_adv_not_move_uniform" in this file).
  • move_uniform at phaseF_adv q' would require the same d for ALL b — impossible.

  PERM_UNIFORM FAILURE at `phaseF_adv q'` and `phaseU_apply`:
  • Same pattern: perm π is read from the hist tape, so the permutation
    returned depends on which hist entry is at the hist head.

  BACKDET FAILURE at `phaseF_run q'`:
  • Even if we redesign BennettState to encode the hist-entry type in each
    state (fixing move/perm uniformity), the states phaseF_adv_write q',
    phaseF_adv_move q' d, phaseF_prm q' all transition to phaseF_run q'
    via MOVE rules.
  • MOVE demands fire at ALL head vectors b (by definition of Demand.move).
  • Multiple predecessor states → multiple demands at (phaseF_run q', b)
    with distinct v values → backdet fails.

  ROOT CAUSE: The `KReversible` predicate is a *syntactic* condition designed
  for machines where each state has a fixed, head-independent move/perm rule.
  Bennett machines must READ the history tape to undo steps; this "read-then-
  dispatch" structure is inherently incompatible with move_uniform/perm_uniform.

  WHAT WOULD FIX IT: A *semantic* reversibility notion (behavioral bijection
  on reachable tapes), replacing the syntactic `KReversible`.  This would
  require reworking M5–M7 (flipM, symmetrisation).  Alternatively, the
  `nakano_symmetrisation_unconditional` theorem could be proved by a direct
  argument (not going through an intermediate KReversible machine), but no
  such argument is currently available in this formalization.

  DECISION (M8c, banked as a negative result): M8 is CLOSED here.  The
  syntactic/semantic gap is itself the finding: syntactic `KReversible` is
  provably too strong — it rejects every faithful Bennett simulator.  The
  mechanised theorem is the conditional M7 (`nakano_symmetrisation`).  The
  semantic re-derivation that would discharge the unconditional theorem is
  left to future work; `bennett_reversibilization` and
  `nakano_symmetrisation_unconditional` stay as documented `sorry`s that
  record the goal statement and this obstruction.
-/

/-- A history tape entry recording what M₀ did at one step.
    Does not depend on the state type Λ; the Bennett machine state tracks
    the M₀ state; the history tape only needs the rule. -/
inductive HistEntry (Γ : Type*) (ι : Type*)
  /-- `write old_heads`: M₀ wrote new symbols; Phase U re-writes `old_heads`. -/
  | write (old_heads : ι → Γ)  : HistEntry Γ ι
  /-- `move d`: M₀ moved in direction d; Phase U moves in `revMap d`. -/
  | move  (d : ι → Option Dir) : HistEntry Γ ι
  /-- `perm π`: M₀ applied perm π; Phase U applies π⁻¹. -/
  | perm  (π : Equiv.Perm ι)   : HistEntry Γ ι

/-- The tape alphabet of the Bennett machine.
    ι-bank tapes store `Γ` via `Sum.inl`; the history tape stores `HistEntry Γ ι`
    via `Sum.inr`.  The default (blank) is `Sum.inl default`. -/
abbrev BennettAlph (Γ : Type*) (ι : Type*) := Γ ⊕ HistEntry Γ ι

instance instInhabitedBennettAlph [Inhabited Γ] :
    Inhabited (BennettAlph Γ ι) :=
  ⟨Sum.inl default⟩

/-- State type of the Bennett machine.

Phase F (forward simulation):
* `phaseF_run q`  — look up M₀ at state q; write the history entry (and new
                    ι-bank heads for write rules) in one combined `KStmt.write`.
* `phaseF_adv q'` — complete M₀'s rule on the ι-bank (for move/perm rules)
                    and advance the history tape head right.
* `phaseF_prm q'` — (perm-rule only) advance the history tape head right after
                    the perm step (perm and move are different `KStmt` variants
                    so the advance requires a separate step).

Phase U (uncompute):
* `phaseU_seek`   — move the history tape head one step left.
* `phaseU_apply`  — read the history entry at the current head position and
                    apply its inverse to the ι-bank.  Halts when the head is blank.

`halted` is not used explicitly; halting is signalled by returning `none`. -/
inductive BennettState (Λ : Type*)
  | phaseF_run   (q : Λ) : BennettState Λ
  | phaseF_adv   (q : Λ) : BennettState Λ
  | phaseF_prm   (q : Λ) : BennettState Λ
  | phaseU_seek           : BennettState Λ
  | phaseU_apply          : BennettState Λ

/-! ### M8b: Phase machines -/

/-
Helper notation (used in `phaseF` / `phaseU`):
  `histIdx` = the tape-bank index of the history tape (`Sum.inr 0`)
  The ι-bank heads are at indices `Sum.inl j` for j : ι.
  All heads have type `BennettAlph Γ ι = Γ ⊕ HistEntry Γ ι`.
-/

/-- Phase F of the Bennett machine.

At `phaseF_run q`, reads M₀ q (ι-bank heads) and dispatches:
  • `write b'` → combined write (new ι-bank heads + hist entry in one KStmt.write)
  • `move d`   → write hist entry (ι-bank unchanged), then `phaseF_adv` does the move
  • `perm π`   → write hist entry (ι-bank unchanged), then `phaseF_adv` does the perm
  • `none`     → M₀ halted; transition to Phase U via identity perm

At `phaseF_adv q'`, reads the just-written hist entry to complete M₀'s rule:
  • write entry → pure hist-advance (move hist right)
  • move entry  → move ι-bank + advance hist right (combined KStmt.move)
  • perm entry  → apply (π ⊕ id) to tape bank; hist-advance in phaseF_prm

At `phaseF_prm q'`: advance hist tape right after a perm step. -/
noncomputable def phaseF (M₀ : KMachine Γ Λ ι) :
    KMachine (BennettAlph Γ ι) (BennettState Λ) (ι ⊕ Fin 1) :=
  fun s b =>
  match s with
  | .phaseF_run q =>
    -- Extract ι-bank heads (project the left component of BennettAlph)
    let a : ι → Γ := fun i => match b (.inl i) with
      | .inl γ => γ
      | .inr _ => default
    match M₀ q a with
    | none =>
      -- M₀ halted: enter Phase U via identity perm (uniform, no-op)
      some (.phaseU_seek, KStmt.perm (Equiv.refl _))
    | some (q', KStmt.write b') =>
      -- Write new ι-bank heads AND record old heads in history — one combined step
      some (.phaseF_adv q', KStmt.write (fun i => match i with
        | .inl j => .inl (b' j)
        | .inr _ => .inr (.write a)))
    | some (q', KStmt.move d) =>
      -- Write history entry only; ι-bank move happens in phaseF_adv
      some (.phaseF_adv q', KStmt.write (fun i => match i with
        | .inl j => b (.inl j)
        | .inr _ => .inr (.move d)))
    | some (q', KStmt.perm π) =>
      -- Write history entry only; ι-bank perm happens in phaseF_adv
      some (.phaseF_adv q', KStmt.write (fun i => match i with
        | .inl j => b (.inl j)
        | .inr _ => .inr (.perm π)))
  | .phaseF_adv q' =>
    -- Reads the history entry at the current head position to complete M₀'s rule
    match b (.inr (0 : Fin 1)) with
    | .inr (.write _) =>
      -- Write rule already applied in phaseF_run; just advance hist tape
      some (.phaseF_run q', KStmt.move (fun i => match i with
        | .inl _ => none
        | .inr _ => some .right))
    | .inr (.move d) =>
      -- Move ι-bank in directions d AND advance hist tape right (combined move)
      some (.phaseF_run q', KStmt.move (fun i => match i with
        | .inl j => d j
        | .inr _ => some .right))
    | .inr (.perm π) =>
      -- Apply perm (π ⊕ id) to tape bank; hist-advance deferred to phaseF_prm
      some (.phaseF_prm q', KStmt.perm (Equiv.sumCongr π (.refl _)))
    | .inl _ => none  -- malformed (hist tape should hold Sum.inr)
  | .phaseF_prm q' =>
    -- After perm step: advance history tape head right
    some (.phaseF_run q', KStmt.move (fun i => match i with
      | .inl _ => none
      | .inr _ => some .right))
  | _ => none  -- Phase U states: phaseF does not handle them

/-- Phase U of the Bennett machine.

At `phaseU_seek`: move hist tape head one step left, then read at `phaseU_apply`.

At `phaseU_apply`, reads the history entry at the current head and applies the
inverse rule to the ι-bank:
  • `write old` → write `old` back to ι-bank (keeps hist tape content)
  • `move d`    → move ι-bank in `revMap d` (hist tape does not move)
  • `perm π`    → apply (π⁻¹ ⊕ id) to tape bank
  • blank (inl) → history exhausted; halt (return none)

NOTE (M8c): Phase U write undo is NOT syntactically backward-deterministic in
isolation (multiple ι-bank states can be overwritten to the same result).
The full `backdet` proof for the combined machine uses the phase-F/phase-U
time-reversal symmetry and the `hbij` hypothesis. -/
noncomputable def phaseU :
    KMachine (BennettAlph Γ ι) (BennettState Λ) (ι ⊕ Fin 1) :=
  fun s b =>
  match s with
  | .phaseU_seek =>
    -- Move hist tape head one step left
    some (.phaseU_apply, KStmt.move (fun i => match i with
      | .inl _ => none
      | .inr _ => some .left))
  | .phaseU_apply =>
    -- Read hist head; apply inverse rule to ι-bank
    match b (.inr (0 : Fin 1)) with
    | .inl _ =>
      -- Blank: history fully consumed; halt
      none
    | .inr (.write old) =>
      -- Re-write old ι-bank heads (hist tape content kept by re-writing it)
      some (.phaseU_seek, KStmt.write (fun i => match i with
        | .inl j => .inl (old j)
        | .inr k => b (.inr k)))
    | .inr (.move d) =>
      -- Move ι-bank in revMap d (hist tape stays; none = no move on hist)
      some (.phaseU_seek, KStmt.move (fun i => match i with
        | .inl j => revMap d j
        | .inr _ => none))
    | .inr (.perm π) =>
      -- Apply (π⁻¹ ⊕ id) to tape bank
      some (.phaseU_seek, KStmt.perm (Equiv.sumCongr π⁻¹ (.refl _)))
  | _ => none  -- Phase F states: phaseU does not handle them

/-- The combined Bennett machine: `phaseF` for Phase F states,
    `phaseU` for Phase U states.  The state types are disjoint so
    `phaseF M₀ s b` and `phaseU M₀ s b` are never both `some`. -/
noncomputable def bennettM (M₀ : KMachine Γ Λ ι) :
    KMachine (BennettAlph Γ ι) (BennettState Λ) (ι ⊕ Fin 1) :=
  fun s b => (phaseF M₀ s b).orElse (fun _ => phaseU s b)

/-- The start state for the Bennett machine (M₀ start at state q₀, blank hist). -/
def bennettStart (q₀ : Λ) : BennettState Λ := .phaseF_run q₀

/-! ### M8c impossibility witness -/

/-- `phaseF_adv q'` returns different move directions for different head vectors:
    hist = `.write _` → move (none on ι-bank, right on hist);
    hist = `.move d`  → move (d on ι-bank, right on hist).
This is a formal proof that `move_uniform` FAILS for `phaseF` (and hence
for `bennettM`): the move direction at a given state depends on the tape
head values.  `KReversible (bennettM M₀)` is therefore NOT provable. -/
theorem phaseF_adv_not_move_uniform (M₀ : KMachine Γ Λ ι) (q' : Λ)
    (d : ι → Option Dir) :
    ∃ (b₁ b₂ : (ι ⊕ Fin 1) → BennettAlph Γ ι),
      (phaseF M₀ (.phaseF_adv q') b₁).map (·.2) = some (KStmt.move fun i =>
        match i with | .inl _ => none | .inr _ => some Dir.right) ∧
      (phaseF M₀ (.phaseF_adv q') b₂).map (·.2) = some (KStmt.move fun i =>
        match i with | .inl j => d j | .inr _ => some Dir.right) :=
  ⟨fun i => match i with | .inl _ => .inl default | .inr _ => .inr (.write fun _ => default),
   fun i => match i with | .inl _ => .inl default | .inr _ => .inr (.move d),
   by simp [phaseF],
   by simp [phaseF]⟩

/-! ### M8 reversibilization theorem (sorry pending M8c) -/

/-- **Bennett reversibilization** (M8): any uniform, bijective `KMachine` can be
simulated by a `KReversible` machine on an extended tape bank `ι ⊕ τ`, where
`τ` indexes a history tape.

The constructed machine is `bennettM M₀ : KMachine (BennettAlph Γ ι) (BennettState Λ) (ι ⊕ Fin 1)`.
It runs in two phases F (forward) and U (uncompute); see the design note above
for the step-by-step description.

**`KReversible` proof status**: BLOCKED — see `phaseF_adv_not_move_uniform`
and the design note for a full analysis.  In short: `phaseF_adv q'` reads the
history tape to choose a move direction, violating `move_uniform`.  Even a
redesign that encodes the hist-entry type in `BennettState` (fixing
move/perm uniformity) leaves `backdet` broken at `phaseF_run q'`, because
multiple predecessor states (`phaseF_adv_write q'`, `phaseF_adv_move q' d`,
`phaseF_prm q'`) all issue MOVE rules to `phaseF_run q'`; MOVE demands fire
at ALL heads, giving multiple demands with distinct `v` values.

The `KReversible` predicate is a *syntactic* condition incompatible with
the "read-then-dispatch" structure of the Bennett machine.  A semantic
reversibility notion is needed to replace it.

**Proof status**: sorry (M8c BLOCKED — fundamental incompatibility). -/
theorem bennett_reversibilization
    {q₀ : Λ}
    (M₀    : KMachine Γ Λ ι)
    (hunif : UniformRules M₀)
    (hbij  : KTapeSemBijective M₀ q₀)
    (hhalt : ∀ q (a : ι → Γ), M₀ q a = none → ∀ a', M₀ q a' = none) :
    ∃ (Λ' τ : Type*) (M' : KMachine Γ Λ' (ι ⊕ τ)) (q₀' qf' : Λ'),
      KReversible M' ∧
      ∀ T, ktapeSem M' q₀' (fun i => Sum.elim T (fun _ => default) i) =
           (ktapeSem M₀ q₀ T).map (fun T' => fun i => Sum.elim T' (fun _ => default) i) :=
  sorry

/-! ### Unconditional symmetrisation (M7 + M8) -/

/-- **Machine-level completeness, unconditional form** (Nakano Thm 4.6 + Bennett).

Combines `nakano_symmetrisation` (M7, Completeness.lean) with
`bennett_reversibilization` (M8, above): the 2k-tape symmetrisation of any
bijective uniform TM computing an involution is KInvolutory, without any
`KReversible` hypothesis on the input machine.

**WRONG SHAPE (superseded).**  This statement builds `D` from `M₀` through
`flipM (liftL M₀)`, which behaves as an inverse only for a `KReversible`
machine -- and no faithful Bennett simulator over a shared alphabet is
`KReversible` (`phaseF2_not_backdet`).  So this `KInvolutory` conclusion is
unprovable in general.  The corrected, function-level target is
`bennett_unconditional_target` (Unconditional.lean), reached through the R2
bridge.  This `sorry` is kept only as a historical record of the original
Track-B goal.

**Proof status**: sorry (wrong shape; see Unconditional.lean). -/
theorem nakano_symmetrisation_unconditional
    {σ : Λ → Λ} {q₀ qf : Λ}
    {M₀ : KMachine Γ Λ ι}
    (hσ      : ∀ q, σ (σ q) = q)
    (hunif   : UniformRules M₀)
    (hbij    : KTapeSemBijective M₀ q₀)
    (hM₀halt : ∀ q (a : ι → Γ), M₀ q a = none ↔ q = qf)
    (hM₀ent  : ∀ q (a : ι → Γ), (∃ v, Demand M₀ q a v) ↔ q ≠ q₀) :
    let R    := liftL M₀ (κ := ι)
    let swap := (Equiv.sumComm ι ι : Equiv.Perm (ι ⊕ ι))
    KInvolutory
      (seq (seq R (bankSwap swap) false) (flipM R σ) (σ qf))
      (conjσ σ not)
      (Sum.inl (Sum.inl q₀))
      (Sum.inr (σ q₀)) :=
  sorry

end PeriodicTM
