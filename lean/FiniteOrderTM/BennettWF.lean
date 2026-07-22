/-
FiniteOrderTM/BennettWF.lean

Track B, milestone M8d (approach (b): semantic reversibility).

The descriptor-encoding Bennett simulator `phaseF2` is not syntactically
`KReversible` — work cells can carry history-symbol junk that write rules
discard (`phaseF2_not_backdet`).  But it IS backward-deterministic on
WELL-FORMED configurations (`phaseF2_backdet_on_wf`), where every work cell is
a `Sum.inl`.  This file supplies the missing half of the semantic story:

  `phaseF2_WF_preserved` — well-formedness is a `kstep`-invariant.

Together they say: on any run from a well-formed configuration, every
configuration — hence every head vector — is well-formed, so backward
determinism holds throughout.  The simulator is reversible on its reachable
configurations, which is exactly the semantic reversibility notion that
approach (b) puts in place of the (too strong) syntactic `KReversible`.

Well-formedness is phrased as being in the image of `Tape.map (Sum.inl)`, so
`Tape.map_write` / `Tape.map_move` carry it through the tape operations with no
dependent-type transport (the friction that ruled out approach (a)).
-/
import FiniteOrderTM.BennettReversible

namespace PeriodicTM

open Turing

variable {Γ : Type*} [Inhabited Γ]
variable {Λ : Type*}
variable {ι : Type*}

/-- The pointed inclusion of the work alphabet into the Bennett alphabet. -/
def inlMap : PointedMap Γ (BennettAlph2 Γ Λ ι) := ⟨Sum.inl, rfl⟩

/-- A tape is well-formed if it is the `Sum.inl`-image of a `Γ`-tape: every cell
is a work symbol, with no history-symbol (`Sum.inr`) junk. -/
def WFtape (T : Tape (BennettAlph2 Γ Λ ι)) : Prop := ∃ T0 : Tape Γ, T = Tape.map inlMap T0

/-- Every work bank of the bundle is well-formed. -/
def WFtapes (T : (ι ⊕ Fin 1) → Tape (BennettAlph2 Γ Λ ι)) : Prop :=
  ∀ j : ι, WFtape (T (Sum.inl j))

theorem WFtape.head_inl {T : Tape (BennettAlph2 Γ Λ ι)} (h : WFtape T) :
    ∃ x, T.head = Sum.inl x := by
  obtain ⟨T0, rfl⟩ := h; exact ⟨T0.head, rfl⟩

theorem WFtape.write_inl {T : Tape (BennettAlph2 Γ Λ ι)} (h : WFtape T) (x : Γ) :
    WFtape (T.write (Sum.inl x)) := by
  obtain ⟨T0, rfl⟩ := h
  exact ⟨T0.write x, by rw [Tape.map_write]; rfl⟩

theorem WFtape.move' {T : Tape (BennettAlph2 Γ Λ ι)} (h : WFtape T) (d : Dir) :
    WFtape (T.move d) := by
  obtain ⟨T0, rfl⟩ := h
  exact ⟨T0.move d, by rw [Tape.map_move]⟩

/-- A well-formed bundle has a well-formed head vector — connecting `WFtapes`
to the `WFvec` hypothesis of `phaseF2_backdet_on_wf`. -/
theorem WFtapes.toWFvec {T : (ι ⊕ Fin 1) → Tape (BennettAlph2 Γ Λ ι)} (h : WFtapes T) :
    WFvec (headsV T) := fun j => (h j).head_inl

theorem WFtapes.write {T : (ι ⊕ Fin 1) → Tape (BennettAlph2 Γ Λ ι)}
    {W : (ι ⊕ Fin 1) → BennettAlph2 Γ Λ ι} (h : WFtapes T)
    (hW : ∀ j, ∃ x, W (Sum.inl j) = Sum.inl x) :
    WFtapes ((KStmt.write W).apply T) := by
  intro j; obtain ⟨x, hx⟩ := hW j
  show WFtape ((T (Sum.inl j)).write (W (Sum.inl j)))
  rw [hx]; exact (h j).write_inl x

theorem WFtapes.move {T : (ι ⊕ Fin 1) → Tape (BennettAlph2 Γ Λ ι)}
    {d : (ι ⊕ Fin 1) → Option Dir} (h : WFtapes T) :
    WFtapes ((KStmt.move d).apply T) := by
  intro j
  show WFtape (match d (Sum.inl j) with | none => T (Sum.inl j) | some dir => (T (Sum.inl j)).move dir)
  cases d (Sum.inl j) with
  | none => exact h j
  | some dir => exact (h j).move' dir

theorem WFtapes.perm_sumCongr {T : (ι ⊕ Fin 1) → Tape (BennettAlph2 Γ Λ ι)}
    {π : Equiv.Perm ι} (h : WFtapes T) :
    WFtapes ((KStmt.perm (Equiv.sumCongr π (Equiv.refl (Fin 1)))).apply T) := by
  intro j
  show WFtape (T ((Equiv.sumCongr π (Equiv.refl (Fin 1)))⁻¹ (Sum.inl j)))
  have he : (Equiv.sumCongr π (Equiv.refl (Fin 1)))⁻¹ (Sum.inl j) = Sum.inl (π⁻¹ j) := by
    simp [Equiv.sumCongr]
  rw [he]; exact h (π⁻¹ j)

/-- **Well-formedness is a `kstep`-invariant of the Bennett simulator.**  If the
work banks hold no history-symbol junk, neither do they after a step.  Hence on
any run from a well-formed configuration every head vector is well-formed, and
`phaseF2_backdet_on_wf` applies throughout — the simulator is reversible on its
reachable configurations. -/
theorem phaseF2_WF_preserved [DecidableEq Γ] (M₀ : KMachine Γ Λ ι)
    {c c' : KCfg (BennettAlph2 Γ Λ ι) (BennettState2 Γ Λ ι) (ι ⊕ Fin 1)}
    (hwf : WFtapes c.tapes) (h : kstep (phaseF2 M₀) c = some c') : WFtapes c'.tapes := by
  obtain ⟨q, T⟩ := c
  simp only [kstep] at h
  cases q with
  | A1 q0 =>
    simp only [phaseF2] at h
    split at h
    · simp at h
    · rw [Option.map_some] at h; cases h; exact WFtapes.write hwf (fun j => ⟨_, rfl⟩)
    · rw [Option.map_some] at h; cases h; exact WFtapes.write hwf (fun j => (hwf j).head_inl)
    · rw [Option.map_some] at h; cases h; exact WFtapes.write hwf (fun j => (hwf j).head_inl)
  | S q0 a0 =>
    simp only [phaseF2] at h
    split at h
    · simp at h
    · rw [Option.map_some] at h; cases h; simpa using WFtapes.move hwf
    · rw [Option.map_some] at h; cases h; simpa using WFtapes.move hwf
    · rw [Option.map_some] at h; cases h; simpa using WFtapes.perm_sumCongr hwf
  | S2 q0 a0 =>
    simp only [phaseF2] at h
    split at h
    · simp at h
    · split at h
      · split at h
        · rw [Option.map_some] at h; cases h
          exact WFtapes.write hwf (fun j => (hwf j).head_inl)
        · simp at h
      · simp at h
  | C q0 =>
    simp only [phaseF2] at h
    rw [Option.map_some] at h; cases h; simpa using WFtapes.move hwf

/-- Well-formedness holds throughout any run from a well-formed configuration. -/
theorem phaseF2_WF_preserved_reaches [DecidableEq Γ] (M₀ : KMachine Γ Λ ι)
    {c c' : KCfg (BennettAlph2 Γ Λ ι) (BennettState2 Γ Λ ι) (ι ⊕ Fin 1)}
    (hwf : WFtapes c.tapes)
    (hr : StateTransition.Reaches (kstep (phaseF2 M₀)) c c') : WFtapes c'.tapes := by
  induction hr with
  | refl => exact hwf
  | tail _ hstep ih => exact phaseF2_WF_preserved M₀ ih (Option.mem_def.mp hstep)

/-! ### Config-level backward determinism on well-formed configurations

The rule-level `phaseF2_backdet_on_wf` lifts to the configuration level: on
well-formed configurations, `kstep` is injective.  This is the local backward
determinism that, by `phaseF2_WF_preserved`, holds along every reachable run —
the heart of the semantic reversibility of the descriptor-encoding simulator. -/

/-- Extract the rule fired by a `kstep`. -/
theorem kstep_rule (M : KMachine Γ Λ ι) {c c' : KCfg Γ Λ ι} (h : kstep M c = some c') :
    ∃ st, M c.q (headsV c.tapes) = some (c'.q, st) ∧ c'.tapes = st.apply c.tapes := by
  rcases hr : M c.q (headsV c.tapes) with _ | ⟨q', st⟩
  · rw [kstep, hr] at h; simp at h
  · rw [kstep, hr, Option.map_some, Option.some.injEq] at h
    subst h
    exact ⟨st, by simp [hr], rfl⟩

/-- **`kstep` is injective on well-formed configurations.**  If two well-formed
configurations step to the same successor, they are equal.  (Backward
determinism at the configuration level, from `phaseF2_backdet_on_wf` plus the
cancellation lemmas for write/move/perm.) -/
theorem phaseF2_kstep_inj_on_wf [DecidableEq Γ] (M₀ : KMachine Γ Λ ι)
    {c₁ c₂ c' : KCfg (BennettAlph2 Γ Λ ι) (BennettState2 Γ Λ ι) (ι ⊕ Fin 1)}
    (w₁ : WFtapes c₁.tapes) (w₂ : WFtapes c₂.tapes)
    (h₁ : kstep (phaseF2 M₀) c₁ = some c') (h₂ : kstep (phaseF2 M₀) c₂ = some c') :
    c₁ = c₂ := by
  obtain ⟨st₁, hr₁, ht₁⟩ := kstep_rule _ h₁
  obtain ⟨st₂, hr₂, ht₂⟩ := kstep_rule _ h₂
  have wfw : ∀ (T : (ι ⊕ Fin 1) → Tape (BennettAlph2 Γ Λ ι)), WFtapes T →
      ∀ a : (ι ⊕ Fin 1) → BennettAlph2 Γ Λ ι,
        (KStmt.write (headsV T) : KStmt (BennettAlph2 Γ Λ ι) (ι ⊕ Fin 1)) = KStmt.write a → WFvec a :=
    fun T wT a ha => by injection ha with e; exact e ▸ wT.toWFvec
  have vacm : ∀ (d : (ι ⊕ Fin 1) → Option Dir) (a : (ι ⊕ Fin 1) → BennettAlph2 Γ Λ ι),
      (KStmt.move d : KStmt (BennettAlph2 Γ Λ ι) (ι ⊕ Fin 1)) = KStmt.write a → WFvec a :=
    fun d a ha => by simp at ha
  have vacp : ∀ (π : Equiv.Perm (ι ⊕ Fin 1)) (a : (ι ⊕ Fin 1) → BennettAlph2 Γ Λ ι),
      (KStmt.perm π : KStmt (BennettAlph2 Γ Λ ι) (ι ⊕ Fin 1)) = KStmt.write a → WFvec a :=
    fun π a ha => by simp at ha
  cases st₁ with
  | write b₁ =>
    have hb₁ : headsV c'.tapes = b₁ := by rw [ht₁]; exact headsV_write _ _
    have D₁ : Demand (phaseF2 M₀) c'.q (headsV c'.tapes) (c₁.q, KStmt.write (headsV c₁.tapes)) := by
      rw [hb₁]; exact Demand.write hr₁
    cases st₂ with
    | write b₂ =>
      have hb₂ : headsV c'.tapes = b₂ := by rw [ht₂]; exact headsV_write _ _
      have D₂ : Demand (phaseF2 M₀) c'.q (headsV c'.tapes) (c₂.q, KStmt.write (headsV c₂.tapes)) := by
        rw [hb₂]; exact Demand.write hr₂
      have hv := phaseF2_backdet_on_wf M₀ D₁ D₂ (wfw _ w₁) (wfw _ w₂)
      obtain ⟨hq, hw⟩ := Prod.mk.injEq .. ▸ hv
      injection hw with hh
      have rec₁ : (KStmt.write (headsV c₁.tapes)).apply c'.tapes = c₁.tapes := by
        rw [ht₁]; exact write_write_cancel _ _
      have rec₂ : (KStmt.write (headsV c₂.tapes)).apply c'.tapes = c₂.tapes := by
        rw [ht₂]; exact write_write_cancel _ _
      cases c₁; cases c₂; simp_all
    | move d₂ =>
      have D₂ : Demand (phaseF2 M₀) c'.q (headsV c'.tapes) (c₂.q, KStmt.move (revMap d₂)) :=
        Demand.move _ hr₂
      have hv := phaseF2_backdet_on_wf M₀ D₁ D₂ (wfw _ w₁) (vacm _); simp at hv
    | perm π₂ =>
      have D₂ : Demand (phaseF2 M₀) c'.q (headsV c'.tapes) (c₂.q, KStmt.perm π₂⁻¹) :=
        Demand.perm _ hr₂
      have hv := phaseF2_backdet_on_wf M₀ D₁ D₂ (wfw _ w₁) (vacp _); simp at hv
  | move d₁ =>
    have D₁ : Demand (phaseF2 M₀) c'.q (headsV c'.tapes) (c₁.q, KStmt.move (revMap d₁)) :=
      Demand.move _ hr₁
    cases st₂ with
    | write b₂ =>
      have hb₂ : headsV c'.tapes = b₂ := by rw [ht₂]; exact headsV_write _ _
      have D₂ : Demand (phaseF2 M₀) c'.q (headsV c'.tapes) (c₂.q, KStmt.write (headsV c₂.tapes)) := by
        rw [hb₂]; exact Demand.write hr₂
      have hv := phaseF2_backdet_on_wf M₀ D₁ D₂ (vacm _) (wfw _ w₂); simp at hv
    | move d₂ =>
      have D₂ : Demand (phaseF2 M₀) c'.q (headsV c'.tapes) (c₂.q, KStmt.move (revMap d₂)) :=
        Demand.move _ hr₂
      have hv := phaseF2_backdet_on_wf M₀ D₁ D₂ (vacm _) (vacm _)
      obtain ⟨hq, hm⟩ := Prod.mk.injEq .. ▸ hv
      injection hm with hh
      have rec₁ : (KStmt.move (revMap d₁)).apply c'.tapes = c₁.tapes := by
        rw [ht₁]; exact move_cancel _ _
      have rec₂ : (KStmt.move (revMap d₂)).apply c'.tapes = c₂.tapes := by
        rw [ht₂]; exact move_cancel _ _
      cases c₁; cases c₂; simp_all
    | perm π₂ =>
      have D₂ : Demand (phaseF2 M₀) c'.q (headsV c'.tapes) (c₂.q, KStmt.perm π₂⁻¹) :=
        Demand.perm _ hr₂
      have hv := phaseF2_backdet_on_wf M₀ D₁ D₂ (vacm _) (vacp _); simp at hv
  | perm π₁ =>
    have D₁ : Demand (phaseF2 M₀) c'.q (headsV c'.tapes) (c₁.q, KStmt.perm π₁⁻¹) :=
      Demand.perm _ hr₁
    cases st₂ with
    | write b₂ =>
      have hb₂ : headsV c'.tapes = b₂ := by rw [ht₂]; exact headsV_write _ _
      have D₂ : Demand (phaseF2 M₀) c'.q (headsV c'.tapes) (c₂.q, KStmt.write (headsV c₂.tapes)) := by
        rw [hb₂]; exact Demand.write hr₂
      have hv := phaseF2_backdet_on_wf M₀ D₁ D₂ (vacp _) (wfw _ w₂); simp at hv
    | move d₂ =>
      have D₂ : Demand (phaseF2 M₀) c'.q (headsV c'.tapes) (c₂.q, KStmt.move (revMap d₂)) :=
        Demand.move _ hr₂
      have hv := phaseF2_backdet_on_wf M₀ D₁ D₂ (vacp _) (vacm _); simp at hv
    | perm π₂ =>
      have D₂ : Demand (phaseF2 M₀) c'.q (headsV c'.tapes) (c₂.q, KStmt.perm π₂⁻¹) :=
        Demand.perm _ hr₂
      have hv := phaseF2_backdet_on_wf M₀ D₁ D₂ (vacp _) (vacp _)
      obtain ⟨hq, hp⟩ := Prod.mk.injEq .. ▸ hv
      injection hp with hh
      have rec₁ : (KStmt.perm π₁⁻¹).apply c'.tapes = c₁.tapes := by
        rw [ht₁]; exact perm_cancel _ _
      have rec₂ : (KStmt.perm π₂⁻¹).apply c'.tapes = c₂.tapes := by
        rw [ht₂]; exact perm_cancel _ _
      cases c₁; cases c₂; simp_all

/-! ### Run-level backward determinism (equal length)

`kstep`-injectivity lifts along runs: two well-formed configurations that reach
a common configuration in the SAME number of steps are equal.  No entry/halt
condition is needed (those enter only when matching run lengths, the next
step toward `ktapeSem` injectivity). -/

/-- `reachesN M n c c'`: `c` reaches `c'` in exactly `n` steps. -/
def reachesN (M : KMachine Γ Λ ι) : ℕ → KCfg Γ Λ ι → KCfg Γ Λ ι → Prop
  | 0 => fun c c' => c = c'
  | n+1 => fun c c' => ∃ c'', kstep M c = some c'' ∧ reachesN M n c'' c'

theorem reachesN_snoc (M : KMachine Γ Λ ι) {n : ℕ} {c b c'' : KCfg Γ Λ ι}
    (h : reachesN M n c b) (hs : kstep M b = some c'') : reachesN M (n+1) c c'' := by
  induction n generalizing c with
  | zero => simp only [reachesN] at h ⊢; subst h; exact ⟨c'', hs, rfl⟩
  | succ n ih =>
    simp only [reachesN] at h ⊢
    obtain ⟨x, hx, hr⟩ := h
    exact ⟨x, hx, ih hr⟩

/-- Every `Reaches` run has a definite length. -/
theorem reaches_to_reachesN (M : KMachine Γ Λ ι) {c c' : KCfg Γ Λ ι}
    (h : StateTransition.Reaches (kstep M) c c') : ∃ n, reachesN M n c c' := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hs ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n+1, reachesN_snoc M hn (Option.mem_def.mp hs)⟩

/-- Split a run of length `a + b` at the `a`-th step. -/
theorem reachesN_split (M : KMachine Γ Λ ι) {a b : ℕ} {c c' : KCfg Γ Λ ι}
    (h : reachesN M (a + b) c c') :
    ∃ m, reachesN M a c m ∧ reachesN M b m c' := by
  induction a generalizing c with
  | zero => exact ⟨c, rfl, by simpa using h⟩
  | succ a ih =>
    rw [Nat.succ_add] at h
    simp only [reachesN] at h ⊢
    obtain ⟨c'', hs, hr⟩ := h
    obtain ⟨m, hm₁, hm₂⟩ := ih hr
    exact ⟨m, ⟨c'', hs, hm₁⟩, hm₂⟩

/-- A nonempty run exhibits a predecessor of its endpoint. -/
theorem reachesN_pred (M : KMachine Γ Λ ι) {d : ℕ} {c c' : KCfg Γ Λ ι}
    (h : reachesN M d c c') (hd : d ≠ 0) : ∃ m, kstep M m = some c' := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  obtain ⟨m, _, hm₂⟩ := reachesN_split M (a := e) (b := 1) h
  simp only [reachesN] at hm₂
  obtain ⟨x, hx, hxe⟩ := hm₂
  exact ⟨m, hxe ▸ hx⟩

/-- **Equal-length backward determinism on well-formed configurations.**  Two
well-formed configurations that reach a common configuration in the SAME number
of steps are equal.  (By induction on the length, from
`phaseF2_kstep_inj_on_wf` + `phaseF2_WF_preserved`.) -/
theorem phaseF2_reachesN_inj_on_wf [DecidableEq Γ] (M₀ : KMachine Γ Λ ι) {n : ℕ}
    {c₁ c₂ cf : KCfg (BennettAlph2 Γ Λ ι) (BennettState2 Γ Λ ι) (ι ⊕ Fin 1)}
    (w₁ : WFtapes c₁.tapes) (w₂ : WFtapes c₂.tapes)
    (h₁ : reachesN (phaseF2 M₀) n c₁ cf) (h₂ : reachesN (phaseF2 M₀) n c₂ cf) :
    c₁ = c₂ := by
  induction n generalizing c₁ c₂ with
  | zero => simp only [reachesN] at h₁ h₂; exact h₁.trans h₂.symm
  | succ n ih =>
    simp only [reachesN] at h₁ h₂
    obtain ⟨c₁'', hs₁, hr₁⟩ := h₁
    obtain ⟨c₂'', hs₂, hr₂⟩ := h₂
    have hc'' : c₁'' = c₂'' :=
      ih (phaseF2_WF_preserved M₀ w₁ hs₁) (phaseF2_WF_preserved M₀ w₂ hs₂) hr₁ hr₂
    subst hc''
    exact phaseF2_kstep_inj_on_wf M₀ w₁ w₂ hs₁ hs₂

/-- Well-formedness is preserved along a `reachesN` run. -/
theorem WFtapes_reachesN [DecidableEq Γ] (M₀ : KMachine Γ Λ ι) {n : ℕ}
    {c c' : KCfg (BennettAlph2 Γ Λ ι) (BennettState2 Γ Λ ι) (ι ⊕ Fin 1)}
    (h : reachesN (phaseF2 M₀) n c c') (w : WFtapes c.tapes) : WFtapes c'.tapes := by
  induction n generalizing c with
  | zero => simp only [reachesN] at h; subst h; exact w
  | succ n ih =>
    simp only [reachesN] at h
    obtain ⟨c'', hs, hr⟩ := h
    exact ih hr (phaseF2_WF_preserved M₀ w hs)

/-- **Backward determinism gives a linear chain.**  If two well-formed configs
reach a common config, the shorter run is a suffix of the longer: the longer's
start reaches the shorter's start in the length difference. -/
theorem phaseF2_reachesN_le_on_wf [DecidableEq Γ] (M₀ : KMachine Γ Λ ι) {n₁ n₂ : ℕ}
    {c₁ c₂ cf : KCfg (BennettAlph2 Γ Λ ι) (BennettState2 Γ Λ ι) (ι ⊕ Fin 1)}
    (h₁ : reachesN (phaseF2 M₀) n₁ c₁ cf) (h₂ : reachesN (phaseF2 M₀) n₂ c₂ cf)
    (hle : n₁ ≤ n₂) (w₁ : WFtapes c₁.tapes) (w₂ : WFtapes c₂.tapes) :
    reachesN (phaseF2 M₀) (n₂ - n₁) c₂ c₁ := by
  have hsplit : reachesN (phaseF2 M₀) ((n₂ - n₁) + n₁) c₂ cf := by
    rwa [Nat.sub_add_cancel hle]
  obtain ⟨m, hm₁, hm₂⟩ := reachesN_split _ hsplit
  have wm : WFtapes m.tapes := WFtapes_reachesN M₀ hm₁ w₂
  have : c₁ = m := phaseF2_reachesN_inj_on_wf M₀ w₁ wm h₁ hm₂
  rw [this]; exact hm₁

/-- **`eval` is injective on well-formed inputs whose start has no predecessor.**
If two well-formed configurations — each with no `kstep`-predecessor — evaluate
to the same halting configuration, they are equal.  (General lemma; the entry
hypotheses `hno₁/hno₂` are the analogue of `nakano_symmetrisation`'s entry
condition.)

CAVEAT for `phaseF2`: `hno₁/hno₂` are NOT satisfiable for a raw `A1` start —
the bi-infinite history tape always admits a head-shifted `C`-predecessor
(`kstep (phaseF2 M₀) ⟨C q, T with history head one cell left⟩ = some ⟨A1 q, T⟩`).
Discharging the entry condition therefore requires either (a) a distinguished
start state with no incoming rule — but a naive `Init` mirroring `A1` breaks
`backdet` at `S` (both feed `S q a` identically), so the start must dispatch to
a separate sub-block; or (b) restricting backward determinism to a
history-structure-invariant subclass of configurations (history head ≥ 0, blank
to the right).  Both are substantial; see ROADMAP M8d. -/
theorem phaseF2_eval_inj_on_wf [DecidableEq Γ] (M₀ : KMachine Γ Λ ι)
    {c₁ c₂ cf : KCfg (BennettAlph2 Γ Λ ι) (BennettState2 Γ Λ ι) (ι ⊕ Fin 1)}
    (w₁ : WFtapes c₁.tapes) (w₂ : WFtapes c₂.tapes)
    (hno₁ : ∀ m, kstep (phaseF2 M₀) m ≠ some c₁)
    (hno₂ : ∀ m, kstep (phaseF2 M₀) m ≠ some c₂)
    (h₁ : cf ∈ StateTransition.eval (kstep (phaseF2 M₀)) c₁)
    (h₂ : cf ∈ StateTransition.eval (kstep (phaseF2 M₀)) c₂) :
    c₁ = c₂ := by
  obtain ⟨hr₁, -⟩ := StateTransition.mem_eval.mp h₁
  obtain ⟨hr₂, -⟩ := StateTransition.mem_eval.mp h₂
  obtain ⟨n₁, hn₁⟩ := reaches_to_reachesN _ hr₁
  obtain ⟨n₂, hn₂⟩ := reaches_to_reachesN _ hr₂
  rcases le_total n₁ n₂ with hle | hle
  · have hsuf := phaseF2_reachesN_le_on_wf M₀ hn₁ hn₂ hle w₁ w₂
    by_cases hd : n₂ - n₁ = 0
    · rw [hd] at hsuf; simp only [reachesN] at hsuf; exact hsuf.symm
    · obtain ⟨m, hm⟩ := reachesN_pred _ hsuf hd; exact absurd hm (hno₁ m)
  · have hsuf := phaseF2_reachesN_le_on_wf M₀ hn₂ hn₁ hle w₂ w₁
    by_cases hd : n₁ - n₂ = 0
    · rw [hd] at hsuf; simp only [reachesN] at hsuf; exact hsuf
    · obtain ⟨m, hm⟩ := reachesN_pred _ hsuf hd; exact absurd hm (hno₂ m)

/-! ### History-structure invariant (toward discharging the entry condition)

The spurious predecessor that makes the entry condition fail is a `C`-config
whose history head is blank.  The real `C`-configs, by contrast, have an ENTRY
under the head (just written by `S2`).  This state-dependent invariant captures
that, plus "blank to the right of the head"; it is forward-preserved, so it
holds along every run from a blank-history start.  Excluding the spurious
predecessor (its head is blank, violating the `C`-clause) is the remaining step
that discharges the entry condition of `phaseF2_eval_inj_on_wf`. -/

/-- History-structure invariant: the history tape is blank from the head
rightward, and the head cell is an entry exactly at `C` states. -/
def HistInv (c : KCfg (BennettAlph2 Γ Λ ι) (BennettState2 Γ Λ ι) (ι ⊕ Fin 1)) : Prop :=
  (c.tapes (Sum.inr 0)).right = default ∧
  (match c.q with
   | .C _ => ∃ e, (c.tapes (Sum.inr 0)).head = Sum.inr e
   | _    => (c.tapes (Sum.inr 0)).head = Sum.inl default)

/-- Any `A1` configuration with a blank history bank satisfies `HistInv`. -/
theorem HistInv_of_blank_hist {q₀ : Λ}
    {Tt : (ι ⊕ Fin 1) → Tape (BennettAlph2 Γ Λ ι)} (hb : Tt (Sum.inr 0) = default) :
    HistInv ⟨BennettState2.A1 q₀, Tt⟩ := by
  refine ⟨?_, ?_⟩
  · show (Tt (Sum.inr 0)).right = default
    rw [hb]; exact ListBlank.ext (congrFun rfl)
  · show (Tt (Sum.inr 0)).head = Sum.inl default
    rw [hb]; rfl

/-- **`HistInv` is forward-preserved by `kstep`.** -/
theorem phaseF2_HistInv_preserved [DecidableEq Γ] (M₀ : KMachine Γ Λ ι)
    {c c' : KCfg (BennettAlph2 Γ Λ ι) (BennettState2 Γ Λ ι) (ι ⊕ Fin 1)}
    (hi : HistInv c) (h : kstep (phaseF2 M₀) c = some c') : HistInv c' := by
  obtain ⟨q, T⟩ := c
  obtain ⟨hr, hh⟩ := hi
  have hidx : ∀ (π : Equiv.Perm ι),
      (Equiv.sumCongr π (Equiv.refl (Fin 1)))⁻¹ (Sum.inr (0:Fin 1)) = Sum.inr 0 :=
    fun π => by simp [Equiv.sumCongr]
  simp only [kstep] at h
  cases q with
  | A1 q0 =>
    simp only [phaseF2] at h
    split at h
    · simp at h
    all_goals
      rw [Option.map_some] at h; cases h
      exact ⟨hr, by simpa only [KStmt.apply, headsV] using hh⟩
  | S q0 a0 =>
    simp only [phaseF2] at h
    split at h
    · simp at h
    · rw [Option.map_some] at h; cases h; exact ⟨hr, hh⟩
    · rw [Option.map_some] at h; cases h; exact ⟨hr, hh⟩
    · rw [Option.map_some] at h; cases h
      exact ⟨by simp only [KStmt.apply, hidx]; exact hr,
             by simp only [KStmt.apply, hidx]; exact hh⟩
  | S2 q0 a0 =>
    simp only [phaseF2] at h
    split at h
    · simp at h
    · split at h
      · split at h
        · rw [Option.map_some] at h; cases h; exact ⟨hr, ⟨_, rfl⟩⟩
        · simp at h
      · simp at h
  | C q0 =>
    simp only [phaseF2] at h
    rw [Option.map_some] at h; cases h
    refine ⟨?_, ?_⟩
    · show ((T (Sum.inr 0)).move Dir.right).right = default
      rw [show ((T (Sum.inr 0)).move Dir.right).right = (T (Sum.inr 0)).right.tail from rfl, hr]
      exact ListBlank.ext (congrFun rfl)
    · show ((T (Sum.inr 0)).move Dir.right).head = Sum.inl default
      rw [show ((T (Sum.inr 0)).move Dir.right).head = (T (Sum.inr 0)).right.head from rfl, hr]
      rfl

/-- `HistInv` holds along a `reachesN` run. -/
theorem HistInv_reachesN [DecidableEq Γ] (M₀ : KMachine Γ Λ ι) {n : ℕ}
    {c c' : KCfg (BennettAlph2 Γ Λ ι) (BennettState2 Γ Λ ι) (ι ⊕ Fin 1)}
    (h : reachesN (phaseF2 M₀) n c c') (hi : HistInv c) : HistInv c' := by
  induction n generalizing c with
  | zero => simp only [reachesN] at h; subst h; exact hi
  | succ n ih =>
    simp only [reachesN] at h
    obtain ⟨c'', hs, hr⟩ := h
    exact ih hr (phaseF2_HistInv_preserved M₀ hi hs)

/-- **No `HistInv` configuration steps to a blank-history `A1` start.**  The
predecessor of an `A1` config is a `C` config (advance), which pushes its head
cell onto the history left; a blank-history target has blank left, forcing that
head to be blank — contradicting `HistInv`'s `C`-clause (entry head).  This is
what makes the entry condition hold for genuine starts. -/
theorem HistInv_no_pred_blank [DecidableEq Γ] (M₀ : KMachine Γ Λ ι) {q₀ : Λ}
    {T₁ : (ι ⊕ Fin 1) → Tape (BennettAlph2 Γ Λ ι)}
    {m : KCfg (BennettAlph2 Γ Λ ι) (BennettState2 Γ Λ ι) (ι ⊕ Fin 1)}
    (hbl : (T₁ (Sum.inr 0)).left = default)
    (hm : HistInv m) (h : kstep (phaseF2 M₀) m = some ⟨BennettState2.A1 q₀, T₁⟩) : False := by
  obtain ⟨mq, mT⟩ := m
  obtain ⟨st, hrule, htapes⟩ := kstep_rule _ h
  have ht : T₁ = st.apply mT := htapes
  have hmq : mq = BennettState2.C q₀ := phaseF2_inv_A1 M₀ hrule
  subst hmq
  obtain ⟨-, hc⟩ := hm
  obtain ⟨e, he⟩ := hc
  simp only [phaseF2] at hrule
  rw [Option.some.injEq, Prod.ext_iff] at hrule
  obtain ⟨-, hst⟩ := hrule
  subst hst
  have hT1 : T₁ (Sum.inr 0) = (mT (Sum.inr 0)).move Dir.right := by rw [ht]; rfl
  rw [hT1, show ((mT (Sum.inr 0)).move Dir.right).left
        = (mT (Sum.inr 0)).left.cons (mT (Sum.inr 0)).head from rfl] at hbl
  have hcontra := congrArg ListBlank.head hbl
  rw [ListBlank.head_cons, he,
     show (default : ListBlank (BennettAlph2 Γ Λ ι)).head = Sum.inl default from rfl] at hcontra
  simp at hcontra

/-- **`eval` is injective on blank-history well-formed inputs.**  Two
blank-history starts that evaluate to the same halting configuration are equal.
The entry condition is discharged by `HistInv` (forward-preserved, and no
`HistInv` config steps to a blank-history start). -/
theorem phaseF2_eval_inj_blank [DecidableEq Γ] (M₀ : KMachine Γ Λ ι) {q₀ : Λ}
    {T₁ T₂ : (ι ⊕ Fin 1) → Tape (BennettAlph2 Γ Λ ι)}
    {cf : KCfg (BennettAlph2 Γ Λ ι) (BennettState2 Γ Λ ι) (ι ⊕ Fin 1)}
    (w₁ : WFtapes T₁) (w₂ : WFtapes T₂)
    (hd₁ : T₁ (Sum.inr 0) = default) (hd₂ : T₂ (Sum.inr 0) = default)
    (h₁ : cf ∈ StateTransition.eval (kstep (phaseF2 M₀)) ⟨BennettState2.A1 q₀, T₁⟩)
    (h₂ : cf ∈ StateTransition.eval (kstep (phaseF2 M₀)) ⟨BennettState2.A1 q₀, T₂⟩) :
    (⟨BennettState2.A1 q₀, T₁⟩ : KCfg (BennettAlph2 Γ Λ ι) (BennettState2 Γ Λ ι) (ι ⊕ Fin 1))
      = ⟨BennettState2.A1 q₀, T₂⟩ := by
  obtain ⟨hr₁, -⟩ := StateTransition.mem_eval.mp h₁
  obtain ⟨hr₂, -⟩ := StateTransition.mem_eval.mp h₂
  obtain ⟨n₁, hn₁⟩ := reaches_to_reachesN _ hr₁
  obtain ⟨n₂, hn₂⟩ := reaches_to_reachesN _ hr₂
  have hi₁ : HistInv (⟨BennettState2.A1 q₀, T₁⟩ : KCfg _ _ _) := HistInv_of_blank_hist hd₁
  have hi₂ : HistInv (⟨BennettState2.A1 q₀, T₂⟩ : KCfg _ _ _) := HistInv_of_blank_hist hd₂
  have hbl₁ : (T₁ (Sum.inr 0)).left = default := by rw [hd₁]; exact ListBlank.ext (congrFun rfl)
  have hbl₂ : (T₂ (Sum.inr 0)).left = default := by rw [hd₂]; exact ListBlank.ext (congrFun rfl)
  rcases le_total n₁ n₂ with hle | hle
  · have hsuf := phaseF2_reachesN_le_on_wf M₀ hn₁ hn₂ hle w₁ w₂
    rcases Nat.eq_zero_or_pos (n₂ - n₁) with hd | hd
    · rw [hd] at hsuf; simp only [reachesN] at hsuf; exact hsuf.symm
    · obtain ⟨e, he⟩ : ∃ e, n₂ - n₁ = e + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hd).symm⟩
      rw [he] at hsuf
      obtain ⟨m, hme, hm1⟩ := reachesN_split _ hsuf
      simp only [reachesN] at hm1
      obtain ⟨x, hx, hxe⟩ := hm1
      exact (HistInv_no_pred_blank M₀ hbl₁ (HistInv_reachesN M₀ hme hi₂) (hxe ▸ hx)).elim
  · have hsuf := phaseF2_reachesN_le_on_wf M₀ hn₂ hn₁ hle w₂ w₁
    rcases Nat.eq_zero_or_pos (n₁ - n₂) with hd | hd
    · rw [hd] at hsuf; simp only [reachesN] at hsuf; exact hsuf
    · obtain ⟨e, he⟩ : ∃ e, n₁ - n₂ = e + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hd).symm⟩
      rw [he] at hsuf
      obtain ⟨m, hme, hm1⟩ := reachesN_split _ hsuf
      simp only [reachesN] at hm1
      obtain ⟨x, hx, hxe⟩ := hm1
      exact (HistInv_no_pred_blank M₀ hbl₂ (HistInv_reachesN M₀ hme hi₁) (hxe ▸ hx)).elim

/-! ### Halt configurations are at `A1` states (toward determining the halt config)

For `ktapeSem` injectivity we need the halt CONFIG (not just its tapes) to be
determined by the output.  A first step: every reachable halting configuration
is at an `A1` state — `S`/`S2` configs do not halt, because they were reached
with `M₀` defined (`NoHaltInv`) and, for `S2`, a blank history head (`HistInv`),
so the rule fires. -/

/-- A `kstep` producing an `S` target has `M₀` defined there. -/
theorem phaseF2_target_S_isSome [DecidableEq Γ] (M₀ : KMachine Γ Λ ι) {p hd q a st}
    (h : phaseF2 M₀ p hd = some (.S q a, st)) : (M₀ q a).isSome := by
  cases p with
  | A1 q0 => simp only [phaseF2] at h; split at h <;> simp_all
  | S q0 a0 => simp only [phaseF2] at h; split at h <;> simp_all
  | S2 q0 a0 => simp only [phaseF2] at h; (repeat' split at h) <;> simp_all
  | C q0 => simp only [phaseF2] at h; simp_all

/-- A `kstep` producing an `S2` target has `M₀` defined there. -/
theorem phaseF2_target_S2_isSome [DecidableEq Γ] (M₀ : KMachine Γ Λ ι) {p hd q a st}
    (h : phaseF2 M₀ p hd = some (.S2 q a, st)) : (M₀ q a).isSome := by
  cases p with
  | A1 q0 => simp only [phaseF2] at h; split at h <;> simp_all
  | S q0 a0 => simp only [phaseF2] at h; split at h <;> simp_all
  | S2 q0 a0 => simp only [phaseF2] at h; (repeat' split at h) <;> simp_all
  | C q0 => simp only [phaseF2] at h; simp_all

/-- Reachable `S`/`S2` configurations have `M₀ q a` defined. -/
def NoHaltInv (M₀ : KMachine Γ Λ ι)
    (c : KCfg (BennettAlph2 Γ Λ ι) (BennettState2 Γ Λ ι) (ι ⊕ Fin 1)) : Prop :=
  (∀ q a, c.q = BennettState2.S q a → (M₀ q a).isSome) ∧
  (∀ q a, c.q = BennettState2.S2 q a → (M₀ q a).isSome)

/-- Any `kstep` result satisfies `NoHaltInv`. -/
theorem phaseF2_NoHaltInv_step [DecidableEq Γ] (M₀ : KMachine Γ Λ ι)
    {c c' : KCfg (BennettAlph2 Γ Λ ι) (BennettState2 Γ Λ ι) (ι ⊕ Fin 1)}
    (h : kstep (phaseF2 M₀) c = some c') : NoHaltInv M₀ c' := by
  obtain ⟨st, hrule, -⟩ := kstep_rule _ h
  refine ⟨fun q a hq => ?_, fun q a hq => ?_⟩
  · rw [hq] at hrule; exact phaseF2_target_S_isSome M₀ hrule
  · rw [hq] at hrule; exact phaseF2_target_S2_isSome M₀ hrule

/-- A reachable halting configuration (`NoHaltInv` + `HistInv`) is at an `A1`
state. -/
theorem phaseF2_halt_is_A1 [DecidableEq Γ] (M₀ : KMachine Γ Λ ι)
    {c : KCfg (BennettAlph2 Γ Λ ι) (BennettState2 Γ Λ ι) (ι ⊕ Fin 1)}
    (hn : NoHaltInv M₀ c) (hh : HistInv c) (h : kstep (phaseF2 M₀) c = none) :
    ∃ q, c.q = BennettState2.A1 q := by
  obtain ⟨q, T⟩ := c
  cases q with
  | A1 q0 => exact ⟨q0, rfl⟩
  | S q0 a0 =>
    obtain ⟨v1, v2, hv⟩ : ∃ v1 v2, M₀ q0 a0 = some (v1, v2) := by
      have hs := hn.1 q0 a0 rfl; rw [Option.isSome_iff_exists] at hs
      obtain ⟨⟨v1, v2⟩, hv⟩ := hs; exact ⟨v1, v2, hv⟩
    simp only [kstep, phaseF2, hv] at h
    cases v2 <;> simp at h
  | S2 q0 a0 =>
    obtain ⟨v1, v2, hv⟩ : ∃ v1 v2, M₀ q0 a0 = some (v1, v2) := by
      have hs := hn.2 q0 a0 rfl; rw [Option.isSome_iff_exists] at hs
      obtain ⟨⟨v1, v2⟩, hv⟩ := hs; exact ⟨v1, v2, hv⟩
    have hb : (T (Sum.inr 0)).head = Sum.inl default := hh.2
    simp only [kstep, phaseF2, hv] at h
    rw [show headsV T (Sum.inr (0:Fin 1)) = Sum.inl default from hb] at h
    simp at h
  | C q0 => simp [kstep, phaseF2] at h

/-! ### State↔history invariant ⇒ `ktapeSem` injectivity

The `A1` halt state is determined by the output tapes: it is the decode of the
top history entry.  `SHInv` captures this (and the `C`-state ↔ head consistency
needed to preserve it).  With it, two blank-history inputs producing the same
output reach the SAME halt config, so `phaseF2_eval_inj_blank` gives equal
inputs: `ktapeSem (phaseF2 M₀)` is injective on blank-history inputs — the
descriptor-encoding simulator computes an injective partial function. -/

/-- Decode the current M₀ state from the top history entry (`q₀` if blank). -/
def decodeTop (M₀ : KMachine Γ Λ ι) (q₀ : Λ) (h : BennettAlph2 Γ Λ ι) : Λ :=
  match h with
  | Sum.inr (HistEntry2.step q a) => (M₀ q a).elim q₀ (·.1)
  | _ => q₀

/-- State↔history invariant: an `A1` state equals the decode of the top history
entry; a `C` state's head holds the entry it came from. -/
def SHInv (M₀ : KMachine Γ Λ ι) (q₀ : Λ)
    (c : KCfg (BennettAlph2 Γ Λ ι) (BennettState2 Γ Λ ι) (ι ⊕ Fin 1)) : Prop :=
  (∀ q, c.q = BennettState2.A1 q → q = decodeTop M₀ q₀ (c.tapes (Sum.inr 0)).left.head) ∧
  (∀ q', c.q = BennettState2.C q' →
    ∃ q a st, (c.tapes (Sum.inr 0)).head = Sum.inr (HistEntry2.step q a) ∧ M₀ q a = some (q', st))

theorem phaseF2_SHInv_preserved [DecidableEq Γ] (M₀ : KMachine Γ Λ ι) (q₀ : Λ)
    {c c' : KCfg (BennettAlph2 Γ Λ ι) (BennettState2 Γ Λ ι) (ι ⊕ Fin 1)}
    (hi : SHInv M₀ q₀ c) (h : kstep (phaseF2 M₀) c = some c') : SHInv M₀ q₀ c' := by
  obtain ⟨q, T⟩ := c
  simp only [kstep] at h
  cases q with
  | A1 q0 =>
    simp only [phaseF2] at h
    split at h
    · simp at h
    all_goals (rw [Option.map_some] at h; cases h
               exact ⟨fun q hq => by simp at hq, fun q' hq' => by simp at hq'⟩)
  | S q0 a0 =>
    simp only [phaseF2] at h
    split at h
    · simp at h
    all_goals (rw [Option.map_some] at h; cases h
               exact ⟨fun q hq => by simp at hq, fun q' hq' => by simp at hq'⟩)
  | S2 q0 a0 =>
    rcases hM : M₀ q0 a0 with _ | ⟨v1, v2⟩
    · simp only [phaseF2, hM] at h; simp at h
    · simp only [phaseF2, hM] at h
      split at h
      · split at h
        · rw [Option.map_some] at h; cases h
          refine ⟨fun q hq => by simp at hq, fun q' hq' => ?_⟩
          injection hq' with hh; subst hh
          exact ⟨q0, a0, v2, rfl, hM⟩
        · simp at h
      · simp at h
  | C q0 =>
    simp only [phaseF2] at h
    rw [Option.map_some] at h; cases h
    refine ⟨fun q hq => ?_, fun q' hq' => by simp at hq'⟩
    obtain ⟨qa, aa, st, hhead, hM⟩ := hi.2 q0 rfl
    injection hq with hq0
    rw [← hq0]
    show q0 = decodeTop M₀ q₀ (((T (Sum.inr 0)).move Dir.right).left.head)
    rw [show ((T (Sum.inr 0)).move Dir.right).left.head = (T (Sum.inr 0)).head from
          ListBlank.head_cons _ _, hhead]
    simp [decodeTop, hM]

theorem SHInv_init (M₀ : KMachine Γ Λ ι) (q₀ : Λ)
    {T : (ι ⊕ Fin 1) → Tape (BennettAlph2 Γ Λ ι)} (hd : T (Sum.inr 0) = default) :
    SHInv M₀ q₀ ⟨BennettState2.A1 q₀, T⟩ := by
  refine ⟨fun q hq => ?_, fun q' hq' => by simp at hq'⟩
  injection hq with e; subst e
  show q₀ = decodeTop M₀ q₀ (T (Sum.inr 0)).left.head
  rw [hd]; rfl

theorem SHInv_reaches [DecidableEq Γ] (M₀ : KMachine Γ Λ ι) (q₀ : Λ)
    {c c' : KCfg (BennettAlph2 Γ Λ ι) (BennettState2 Γ Λ ι) (ι ⊕ Fin 1)}
    (hi : SHInv M₀ q₀ c) (hr : StateTransition.Reaches (kstep (phaseF2 M₀)) c c') :
    SHInv M₀ q₀ c' := by
  induction hr with
  | refl => exact hi
  | tail _ hs ih => exact phaseF2_SHInv_preserved M₀ q₀ ih (Option.mem_def.mp hs)

theorem NoHaltInv_A1 (M₀ : KMachine Γ Λ ι) (q₀ : Λ)
    (T : (ι ⊕ Fin 1) → Tape (BennettAlph2 Γ Λ ι)) :
    NoHaltInv M₀ ⟨BennettState2.A1 q₀, T⟩ :=
  ⟨fun q a hq => by simp at hq, fun q a hq => by simp at hq⟩

theorem NoHaltInv_reaches [DecidableEq Γ] (M₀ : KMachine Γ Λ ι)
    {c c' : KCfg (BennettAlph2 Γ Λ ι) (BennettState2 Γ Λ ι) (ι ⊕ Fin 1)}
    (hi : NoHaltInv M₀ c) (hr : StateTransition.Reaches (kstep (phaseF2 M₀)) c c') :
    NoHaltInv M₀ c' := by
  induction hr with
  | refl => exact hi
  | tail _ hs _ => exact phaseF2_NoHaltInv_step M₀ (Option.mem_def.mp hs)

theorem HistInv_reaches [DecidableEq Γ] (M₀ : KMachine Γ Λ ι)
    {c c' : KCfg (BennettAlph2 Γ Λ ι) (BennettState2 Γ Λ ι) (ι ⊕ Fin 1)}
    (hi : HistInv c) (hr : StateTransition.Reaches (kstep (phaseF2 M₀)) c c') :
    HistInv c' := by
  induction hr with
  | refl => exact hi
  | tail _ hs ih => exact phaseF2_HistInv_preserved M₀ ih (Option.mem_def.mp hs)

/-- **`ktapeSem (phaseF2 M₀)` is injective on blank-history well-formed inputs.**
The descriptor-encoding Bennett simulator computes an injective partial function
of its (blank-history) input — the Axelsen–Glück reversibility characterisation,
on reachable inputs, with NO bijectivity hypothesis on M₀. -/
theorem phaseF2_ktapeSem_inj [DecidableEq Γ] (M₀ : KMachine Γ Λ ι) (q₀ : Λ)
    {T₁ T₂ Tout : (ι ⊕ Fin 1) → Tape (BennettAlph2 Γ Λ ι)}
    (w₁ : WFtapes T₁) (w₂ : WFtapes T₂)
    (hd₁ : T₁ (Sum.inr 0) = default) (hd₂ : T₂ (Sum.inr 0) = default)
    (h₁ : Tout ∈ ktapeSem (phaseF2 M₀) (BennettState2.A1 q₀) T₁)
    (h₂ : Tout ∈ ktapeSem (phaseF2 M₀) (BennettState2.A1 q₀) T₂) :
    T₁ = T₂ := by
  obtain ⟨cf₁, hcf₁, htf₁⟩ := (Part.mem_map_iff _).mp h₁
  obtain ⟨cf₂, hcf₂, htf₂⟩ := (Part.mem_map_iff _).mp h₂
  obtain ⟨hreach₁, hhalt₁⟩ := StateTransition.mem_eval.mp hcf₁
  obtain ⟨hreach₂, hhalt₂⟩ := StateTransition.mem_eval.mp hcf₂
  have sh₁ := SHInv_reaches M₀ q₀ (SHInv_init M₀ q₀ hd₁) hreach₁
  have sh₂ := SHInv_reaches M₀ q₀ (SHInv_init M₀ q₀ hd₂) hreach₂
  have nh₁ := NoHaltInv_reaches M₀ (NoHaltInv_A1 M₀ q₀ T₁) hreach₁
  have nh₂ := NoHaltInv_reaches M₀ (NoHaltInv_A1 M₀ q₀ T₂) hreach₂
  have hh₁ := HistInv_reaches M₀ (HistInv_of_blank_hist hd₁) hreach₁
  have hh₂ := HistInv_reaches M₀ (HistInv_of_blank_hist hd₂) hreach₂
  obtain ⟨qf₁, hqf₁⟩ := phaseF2_halt_is_A1 M₀ nh₁ hh₁ hhalt₁
  obtain ⟨qf₂, hqf₂⟩ := phaseF2_halt_is_A1 M₀ nh₂ hh₂ hhalt₂
  have htapes : cf₁.tapes = cf₂.tapes := by rw [htf₁, htf₂]
  have hqfeq : qf₁ = qf₂ := by rw [sh₁.1 qf₁ hqf₁, sh₂.1 qf₂ hqf₂, htapes]
  have hqeq : cf₁.q = cf₂.q := by rw [hqf₁, hqf₂, hqfeq]
  have hcfeq : cf₁ = cf₂ := by
    obtain ⟨q1, T1⟩ := cf₁; obtain ⟨q2, T2⟩ := cf₂
    obtain rfl : q1 = q2 := hqeq
    obtain rfl : T1 = T2 := htapes
    rfl
  have heq := phaseF2_eval_inj_blank M₀ w₁ w₂ hd₁ hd₂ hcf₁ (hcfeq ▸ hcf₂)
  exact congrArg KCfg.tapes heq

end PeriodicTM
