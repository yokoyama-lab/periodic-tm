/-
FiniteOrderTM/Symmetrise.lean

Track B, milestone M6a: time-reversal distributes over sequential
composition.

Sequential composition is NOT reversible in general: the hand-over merges
every halting state of `M₁` into `M₂`'s start state, which is backward
nondeterministic.  But when `M₁` halts at a *unique* state `qfA`, the
hand-over is a single bridge rule `qfA → q₀B`, which is backward
deterministic, and `seq A B` admits a flip.

The flip of `seq A B` is `seq B' A'` (the components flipped and their
order reversed), under the state map that sends an `A`-state to the
`A'`-block and a `B`-state to the `B'`-block.  Two boundary conditions
make the bridge reverse correctly:

* the start state of the second component of the flipped composite is
  `σA qfA` (the σ-image of where `A` halts);
* `B'` halts at `σB q₀B` (the σ-image of `B`'s start), so the reversed
  bridge fires there.

This is the combinator-level core of Nakano's "involutory machines are
closed under conjugation" (Lemma 4.4).
-/
import FiniteOrderTM.Flip

namespace PeriodicTM

open Turing

variable {Γ : Type*} [Inhabited Γ] {ι : Type*}
variable {ΛA ΛB ΛA' ΛB' : Type*}

/-- State map for the flipped composite: an `A`-state goes to the
`A'`-block (the right side of `seq B' A'`), a `B`-state to the `B'`-block
(the left side). -/
def seqFlipσ (σA : ΛA → ΛA') (σB : ΛB → ΛB') : ΛA ⊕ ΛB → ΛB' ⊕ ΛA'
  | Sum.inl q => Sum.inr (σA q)
  | Sum.inr q => Sum.inl (σB q)

variable {A : KMachine Γ ΛA ι} {B : KMachine Γ ΛB ι}
variable {A' : KMachine Γ ΛA' ι} {B' : KMachine Γ ΛB' ι}
variable {σA : ΛA → ΛA'} {σB : ΛB → ΛB'}

/-! ### Rule-level unfolding of `seq` -/

theorem seq_rule_inl_some {pa pa' : ΛA} {a : ι → Γ} {st : KStmt Γ ι}
    {q0B : ΛB} (e : A pa a = some (pa', st)) :
    seq A B q0B (Sum.inl pa) a = some (Sum.inl pa', st) := by
  simp [seq, e]

theorem seq_rule_inl_none {pa : ΛA} {a : ι → Γ} {q0B : ΛB}
    (e : A pa a = none) :
    seq A B q0B (Sum.inl pa) a = some (Sum.inr q0B, KStmt.write a) := by
  simp [seq, e]

theorem seq_rule_inr {pb : ΛB} {a : ι → Γ} {q0B : ΛB} :
    seq A B q0B (Sum.inr pb) a
      = (B pb a).map fun s => (Sum.inr s.1, s.2) := by
  simp [seq]

/-! ### Flip distributes over `seq` -/

/-- **Milestone M6a**: under unique-halt of `A`, the flip of `seq A B` is
`seq B' A'`. -/
theorem kFlipOf_seq
    (hA : KFlipOf A A' σA) (hB : KFlipOf B B' σB)
    {qfA : ΛA} {q0B : ΛB}
    (haltA : ∀ q a, A q a = none → q = qfA)
    (hB'halt : ∀ a, B' (σB q0B) a = none) :
    KFlipOf (seq A B q0B) (seq B' A' (σA qfA)) (seqFlipσ σA σB) := by
  refine ⟨?_, ?_, ?_⟩
  · -- flip_write
    intro p a q b hrule
    cases p with
    | inl pa =>
        rcases e : A pa a with - | ⟨pa', st⟩
        · -- bridge rule
          rw [seq_rule_inl_none e, Option.some.injEq, Prod.mk.injEq] at hrule
          obtain ⟨hq, hb⟩ := hrule
          have hba : b = a := by simpa using hb.symm
          have hpa : pa = qfA := haltA pa a e
          subst hq; subst hba
          simp [seq, seqFlipσ, hpa, hB'halt]
        · -- A-rule
          rw [seq_rule_inl_some e] at hrule
          obtain ⟨hq, hst⟩ := Prod.mk.injEq .. ▸ Option.some.inj hrule
          subst hq
          cases hst
          show seq B' A' (σA qfA) (Sum.inr (σA pa')) b
            = some (Sum.inr (σA pa), KStmt.write a)
          rw [seq_rule_inr, hA.flip_write pa a pa' b e]
          rfl
    | inr pb =>
        rw [seq_rule_inr] at hrule
        rcases e : B pb a with - | ⟨pb', st⟩
        · rw [e] at hrule; simp at hrule
        · rw [e] at hrule
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hrule
          obtain ⟨hq, hst⟩ := hrule
          subst hq
          cases hst
          show seq B' A' (σA qfA) (Sum.inl (σB pb')) b
            = some (Sum.inl (σB pb), KStmt.write a)
          simp [seq, hB.flip_write pb a pb' b e]
  · -- flip_move
    intro p a q d hrule
    intro bb
    cases p with
    | inl pa =>
        rcases e : A pa a with - | ⟨pa', st⟩
        · rw [seq_rule_inl_none e] at hrule
          simp at hrule
        · rw [seq_rule_inl_some e] at hrule
          obtain ⟨hq, hst⟩ := Prod.mk.injEq .. ▸ Option.some.inj hrule
          subst hq; cases hst
          show seq B' A' (σA qfA) (Sum.inr (σA pa')) bb
            = some (Sum.inr (σA pa), KStmt.move (revMap d))
          simp [seq, hA.flip_move pa a pa' d e bb]
    | inr pb =>
        rw [seq_rule_inr] at hrule
        rcases e : B pb a with - | ⟨pb', st⟩
        · rw [e] at hrule; simp at hrule
        · rw [e] at hrule
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hrule
          obtain ⟨hq, hst⟩ := hrule
          subst hq; cases hst
          show seq B' A' (σA qfA) (Sum.inl (σB pb')) bb
            = some (Sum.inl (σB pb), KStmt.move (revMap d))
          simp [seq, hB.flip_move pb a pb' d e bb]
  · -- flip_perm
    intro p a q π hrule
    intro bb
    cases p with
    | inl pa =>
        rcases e : A pa a with - | ⟨pa', st⟩
        · rw [seq_rule_inl_none e] at hrule
          simp at hrule
        · rw [seq_rule_inl_some e] at hrule
          obtain ⟨hq, hst⟩ := Prod.mk.injEq .. ▸ Option.some.inj hrule
          subst hq; cases hst
          show seq B' A' (σA qfA) (Sum.inr (σA pa')) bb
            = some (Sum.inr (σA pa), KStmt.perm π⁻¹)
          simp [seq, hA.flip_perm pa a pa' π e bb]
    | inr pb =>
        rw [seq_rule_inr] at hrule
        rcases e : B pb a with - | ⟨pb', st⟩
        · rw [e] at hrule; simp at hrule
        · rw [e] at hrule
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hrule
          obtain ⟨hq, hst⟩ := hrule
          subst hq; cases hst
          show seq B' A' (σA qfA) (Sum.inl (σB pb')) bb
            = some (Sum.inl (σB pb), KStmt.perm π⁻¹)
          simp [seq, hB.flip_perm pb a pb' π e bb]

/-! ### M6b: conjugation closure (Lemma 4.4, semantic + syntactic forms)

The conjugate of an involutory machine `M` by a reversible machine `R` is
`D := seq (seq R M) (flipM R)`, which computes
`⟦flipM R⟧ ∘ ⟦M⟧ ∘ ⟦R⟧ = r⁻¹ ∘ m ∘ r`.

**Semantic form** (`conj_partial_involution`): proved by monad algebra
reusing `flipM_tapeSem_inverse` + `KInvolutory.ktapeSem_involutive`.

**Syntactic form** (`conj_KInvolutory`): D is itself a `KInvolutory`
machine under the state map `conjσ`.  The key observation is that the
run-reversal symmetry of D carries R-states to flipM-states (and vice
versa) and M-states to M-states under σM.  The bridge rules (R→M hand-over
and M→flipM hand-over) reverse each other by the identities σM qfM = q0M
and hRhalt.  This avoids seq-associativity and explicit heterogeneous type
isomorphisms: all types stay (ΛR ⊕ ΛM) ⊕ ΛR throughout. -/

variable {ΛR ΛM : Type*}

/-- The conjugate machine computes the threefold composition. -/
theorem conjSem (R : KMachine Γ ΛR ι) (M : KMachine Γ ΛM ι) (σR : ΛR → ΛR)
    (q0R q0M qfR : _) (T : ι → Tape Γ) :
    ktapeSem (seq (seq R M q0M) (flipM R σR) (σR qfR))
        (Sum.inl (Sum.inl q0R)) T
      = ((ktapeSem R q0R T).bind (ktapeSem M q0M)).bind
          (ktapeSem (flipM R σR) (σR qfR)) := by
  rw [ktapeSem_seq, ktapeSem_seq]

/-- **Milestone M6b** (Lemma 4.4, semantic): the conjugate of an
involutory machine by a reversible machine computes a partial involution. -/
theorem conj_partial_involution
    {R : KMachine Γ ΛR ι} {M : KMachine Γ ΛM ι}
    {σR : ΛR → ΛR} {σM : ΛM → ΛM} {q0R qfR : ΛR} {q0M qfM : ΛM}
    (hM : KInvolutory M σM q0M qfM)
    (hσR : ∀ q, σR (σR q) = q) (hRrev : KReversible R)
    (hRhalt : ∀ q a, R q a = none ↔ q = qfR)
    (hRent : ∀ q b, (∃ v, Demand R q b v) ↔ q ≠ q0R)
    {T T' : ι → Tape Γ}
    (h : T' ∈ ktapeSem (seq (seq R M q0M) (flipM R σR) (σR qfR))
        (Sum.inl (Sum.inl q0R)) T) :
    T ∈ ktapeSem (seq (seq R M q0M) (flipM R σR) (σR qfR))
        (Sum.inl (Sum.inl q0R)) T' := by
  have invR : ∀ X Y, Y ∈ ktapeSem R q0R X ↔
      X ∈ ktapeSem (flipM R σR) (σR qfR) Y :=
    fun X Y => flipM_tapeSem_inverse hσR hRrev hRhalt hRent (T := X) (T' := Y)
  rw [conjSem] at h ⊢
  rw [Part.mem_bind_iff] at h
  obtain ⟨V, hV, hT'⟩ := h
  rw [Part.mem_bind_iff] at hV
  obtain ⟨U, hU, hVU⟩ := hV
  -- hU : U ∈ ⟦R⟧ T ; hVU : V ∈ ⟦M⟧ U ; hT' : T' ∈ ⟦flipM R⟧ V
  have hVT' : V ∈ ktapeSem R q0R T' := (invR T' V).mpr hT'
  have hUV : U ∈ ktapeSem M q0M V := hM.ktapeSem_involutive hVU
  have hTU : T ∈ ktapeSem (flipM R σR) (σR qfR) U := (invR T U).mp hU
  rw [Part.mem_bind_iff]
  exact ⟨U, Part.mem_bind_iff.mpr ⟨V, hVT', hUV⟩, hTU⟩

/-! ### M6b syntactic: conjugate is itself KInvolutory -/

/-- State map for the conjugate machine `seq (seq R M) (flipM R)`.
R-states and flipM-states are swapped through σR; M-states are sent to
M-states through σM. -/
def conjσ (σR : ΛR → ΛR) (σM : ΛM → ΛM) :
    (ΛR ⊕ ΛM) ⊕ ΛR → (ΛR ⊕ ΛM) ⊕ ΛR
  | Sum.inl (Sum.inl r) => Sum.inr (σR r)
  | Sum.inl (Sum.inr m) => Sum.inl (Sum.inr (σM m))
  | Sum.inr r           => Sum.inl (Sum.inl (σR r))

/-- **Milestone M6b (syntactic)** (Lemma 4.4): the conjugate machine is itself
involutory.  The state map `conjσ σR σM` swaps the R-block with the
flipM-block, and sends M-states to M-states under σM. -/
theorem conj_KInvolutory
    {R : KMachine Γ ΛR ι} {M : KMachine Γ ΛM ι}
    {σR : ΛR → ΛR} {σM : ΛM → ΛM} {q0R qfR : ΛR} {q0M qfM : ΛM}
    (hM    : KInvolutory M σM q0M qfM)
    (hσR   : ∀ q, σR (σR q) = q)
    (hRrev : KReversible R)
    (hRhalt : ∀ q a, R q a = none ↔ q = qfR)
    (hRent  : ∀ q b, (∃ v, Demand R q b v) ↔ q ≠ q0R) :
    KInvolutory
      (seq (seq R M q0M) (flipM R σR) (σR qfR))
      (conjσ σR σM)
      (Sum.inl (Sum.inl q0R))
      (Sum.inr (σR q0R)) where
  invol := fun q => by
    cases q with
    | inl e => cases e with
      | inl r => simp [conjσ, hσR]
      | inr m => simp [conjσ, hM.invol]
    | inr r => simp [conjσ, hσR]
  start := by simp [conjσ]
  halt_iff := fun q a => by
    cases q with
    | inl e =>
      refine ⟨fun h => ?_, fun h => absurd h (by simp)⟩
      simp only [seq] at h
      cases e with
      | inl r => split at h <;> simp_all
      | inr m => split at h <;> simp_all
    | inr r =>
      simp only [Sum.inr.injEq]
      rw [seq_rule_inr]
      constructor
      · intro h
        rcases hf : flipM R σR r a with _ | s
        · exact (flipM_halt_iff hσR hRent r a).mp hf
        · simp [hf] at h
      · intro h
        subst h
        simp [(flipM_halt_iff hσR hRent (σR q0R) a).mpr rfl]
  flip := by
    have hflipR' := kFlipOf_flipM_rev hσR hRrev
    have hMhalt  := hM.halt_iff
    have hMstart := hM.start
    have hσMqfM : σM qfM = q0M := by
      have := hM.invol q0M; rw [hMstart] at this; exact this
    refine ⟨?_, ?_, ?_⟩
    -- flip_write ----------------------------------------------------------
    · intro p a q b hrule
      cases p with
      | inl ep =>
        cases ep with
        | inl r =>
          rcases eR : R r a with _ | ⟨r', st⟩
          · -- inner bridge: R r a = none → D = some (Sum.inl (Sum.inr q0M), write a)
            rw [seq_rule_inl_some (seq_rule_inl_none eR), Option.some.injEq,
                Prod.mk.injEq] at hrule
            obtain ⟨hq, hb⟩ := hrule
            have hpa : r = qfR := (hRhalt r a).mp eR
            have hab : a = b := KStmt.write.inj hb
            subst hq
            simp only [conjσ, hMstart, hpa, hab]
            exact seq_rule_inl_none (by rw [seq_rule_inr]; simp [(hMhalt qfM b).mpr rfl])
          · -- R rule: D = some (Sum.inl (Sum.inl r'), st)
            rw [seq_rule_inl_some (seq_rule_inl_some eR)] at hrule
            obtain ⟨hq, hst⟩ := Prod.mk.injEq .. ▸ Option.some.inj hrule
            subst hq; cases hst
            -- eR : R r a = some (r', KStmt.write b)
            show seq (seq R M q0M) (flipM R σR) (σR qfR) (Sum.inr (σR r')) b
              = some (Sum.inr (σR r), KStmt.write a)
            rw [seq_rule_inr, flipM_spec hRrev (by rw [hσR]; exact .write eR)]; rfl
        | inr m =>
          rcases eM : M m a with _ | ⟨m', st⟩
          · -- outer bridge: M m a = none → D = some (Sum.inr (σR qfR), write a)
            rw [seq_rule_inl_none (by rw [seq_rule_inr]; simp [eM] :
                  seq R M q0M (Sum.inr m) a = none),
                Option.some.injEq, Prod.mk.injEq] at hrule
            obtain ⟨hq, hb⟩ := hrule
            have hpm : m = qfM := (hMhalt m a).mp eM
            have hab : a = b := KStmt.write.inj hb
            subst hq
            simp only [conjσ, hpm, hσMqfM, hσR, hab]
            exact seq_rule_inl_some (seq_rule_inl_none ((hRhalt qfR b).mpr rfl))
          · -- M rule: D = some (Sum.inl (Sum.inr m'), st)
            rw [seq_rule_inl_some (by rw [seq_rule_inr, eM]; rfl :
                  seq R M q0M (Sum.inr m) a = some (Sum.inr m', st))] at hrule
            obtain ⟨hq, hst⟩ := Prod.mk.injEq .. ▸ Option.some.inj hrule
            subst hq; cases hst
            -- eM : M m a = some (m', KStmt.write b)
            show seq (seq R M q0M) (flipM R σR) (σR qfR) (Sum.inl (Sum.inr (σM m'))) b
              = some (Sum.inl (Sum.inr (σM m)), KStmt.write a)
            exact seq_rule_inl_some (by rw [seq_rule_inr, hM.flip.flip_write m a m' b eM]; rfl)
      | inr r =>
        rw [seq_rule_inr] at hrule
        rcases efM : flipM R σR r a with _ | ⟨r', st⟩
        · simp [efM] at hrule
        · rw [efM, Option.map_some] at hrule
          obtain ⟨hq, hst⟩ := Prod.mk.injEq .. ▸ Option.some.inj hrule
          subst hq; cases hst
          -- efM : flipM R σR r a = some (r', KStmt.write b)
          show seq (seq R M q0M) (flipM R σR) (σR qfR) (Sum.inl (Sum.inl (σR r'))) b
            = some (Sum.inl (Sum.inl (σR r)), KStmt.write a)
          exact seq_rule_inl_some (seq_rule_inl_some (hflipR'.flip_write r a r' b efM))
    -- flip_move ----------------------------------------------------------
    · intro p a q d hrule bb
      cases p with
      | inl ep =>
        cases ep with
        | inl r =>
          rcases eR : R r a with _ | ⟨r', st⟩
          · rw [seq_rule_inl_some (seq_rule_inl_none eR)] at hrule; simp at hrule
          · rw [seq_rule_inl_some (seq_rule_inl_some eR)] at hrule
            obtain ⟨hq, hst⟩ := Prod.mk.injEq .. ▸ Option.some.inj hrule
            subst hq; cases hst
            -- eR : R r a = some (r', KStmt.move d)
            show seq (seq R M q0M) (flipM R σR) (σR qfR) (Sum.inr (σR r')) bb
              = some (Sum.inr (σR r), KStmt.move (revMap d))
            rw [seq_rule_inr, flipM_spec hRrev (by rw [hσR]; exact .move bb eR)]; rfl
        | inr m =>
          rcases eM : M m a with _ | ⟨m', st⟩
          · rw [seq_rule_inl_none (by rw [seq_rule_inr, eM]; rfl :
                  seq R M q0M (Sum.inr m) a = none)] at hrule
            simp at hrule
          · rw [seq_rule_inl_some (by rw [seq_rule_inr, eM]; rfl :
                  seq R M q0M (Sum.inr m) a = some (Sum.inr m', st))] at hrule
            obtain ⟨hq, hst⟩ := Prod.mk.injEq .. ▸ Option.some.inj hrule
            subst hq; cases hst
            -- eM : M m a = some (m', KStmt.move d)
            show seq (seq R M q0M) (flipM R σR) (σR qfR) (Sum.inl (Sum.inr (σM m'))) bb
              = some (Sum.inl (Sum.inr (σM m)), KStmt.move (revMap d))
            exact seq_rule_inl_some (by rw [seq_rule_inr, hM.flip.flip_move m a m' d eM bb]; rfl)
      | inr r =>
        rw [seq_rule_inr] at hrule
        rcases efM : flipM R σR r a with _ | ⟨r', st⟩
        · simp [efM] at hrule
        · rw [efM, Option.map_some] at hrule
          obtain ⟨hq, hst⟩ := Prod.mk.injEq .. ▸ Option.some.inj hrule
          subst hq; cases hst
          -- efM : flipM R σR r a = some (r', KStmt.move d)
          show seq (seq R M q0M) (flipM R σR) (σR qfR) (Sum.inl (Sum.inl (σR r'))) bb
            = some (Sum.inl (Sum.inl (σR r)), KStmt.move (revMap d))
          exact seq_rule_inl_some (seq_rule_inl_some (hflipR'.flip_move r a r' d efM bb))
    -- flip_perm ----------------------------------------------------------
    · intro p a q π hrule bb
      cases p with
      | inl ep =>
        cases ep with
        | inl r =>
          rcases eR : R r a with _ | ⟨r', st⟩
          · rw [seq_rule_inl_some (seq_rule_inl_none eR)] at hrule; simp at hrule
          · rw [seq_rule_inl_some (seq_rule_inl_some eR)] at hrule
            obtain ⟨hq, hst⟩ := Prod.mk.injEq .. ▸ Option.some.inj hrule
            subst hq; cases hst
            -- eR : R r a = some (r', KStmt.perm π)
            show seq (seq R M q0M) (flipM R σR) (σR qfR) (Sum.inr (σR r')) bb
              = some (Sum.inr (σR r), KStmt.perm π⁻¹)
            rw [seq_rule_inr, flipM_spec hRrev (by rw [hσR]; exact .perm bb eR)]; rfl
        | inr m =>
          rcases eM : M m a with _ | ⟨m', st⟩
          · rw [seq_rule_inl_none (by rw [seq_rule_inr, eM]; rfl :
                  seq R M q0M (Sum.inr m) a = none)] at hrule
            simp at hrule
          · rw [seq_rule_inl_some (by rw [seq_rule_inr, eM]; rfl :
                  seq R M q0M (Sum.inr m) a = some (Sum.inr m', st))] at hrule
            obtain ⟨hq, hst⟩ := Prod.mk.injEq .. ▸ Option.some.inj hrule
            subst hq; cases hst
            -- eM : M m a = some (m', KStmt.perm π)
            show seq (seq R M q0M) (flipM R σR) (σR qfR) (Sum.inl (Sum.inr (σM m'))) bb
              = some (Sum.inl (Sum.inr (σM m)), KStmt.perm π⁻¹)
            exact seq_rule_inl_some (by rw [seq_rule_inr, hM.flip.flip_perm m a m' π eM bb]; rfl)
      | inr r =>
        rw [seq_rule_inr] at hrule
        rcases efM : flipM R σR r a with _ | ⟨r', st⟩
        · simp [efM] at hrule
        · rw [efM, Option.map_some] at hrule
          obtain ⟨hq, hst⟩ := Prod.mk.injEq .. ▸ Option.some.inj hrule
          subst hq; cases hst
          -- efM : flipM R σR r a = some (r', KStmt.perm π)
          show seq (seq R M q0M) (flipM R σR) (σR qfR) (Sum.inl (Sum.inl (σR r'))) bb
            = some (Sum.inl (Sum.inl (σR r)), KStmt.perm π⁻¹)
          exact seq_rule_inl_some (seq_rule_inl_some (hflipR'.flip_perm r a r' π efM bb))

end PeriodicTM
