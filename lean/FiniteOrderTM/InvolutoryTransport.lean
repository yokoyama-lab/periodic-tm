/-
FiniteOrderTM/InvolutoryTransport.lean

Roadmap step 2 for `StringConjugationClosure` (see `InvolutoryString.lean`):
the KMachine ↔ TM0 transport, and machine-level conjugation closure at
`tapeSem`.

Contents:

* **The bridge** (priority 1).  A `Unit`-indexed `KMachine` is essentially a
  `TM0` machine.  `toK M` embeds a `TM0` machine as a `Unit`-indexed
  `KMachine`; `ofK K` collapses a `Unit`-indexed `KMachine` to `TM0`
  (translating no-op statements — `move` with no direction, `perm` on the
  one-element bank — into write-back rules `write a`, a semantic no-op).
  The step-exact simulation gives the semantics bridges with *no side
  hypotheses*:

    - `tapeSem_ofK` :
        `tapeSem (ofK K) q₀ T = (ktapeSem K q₀ (fun _ => T)).map (· ())`
    - `ktapeSem_ofK_expand` (the same bijection read the other way), and
    - `ktapeSem_toK` : `ktapeSem (toK M) q₀ (fun _ => T)
                          = (tapeSem M q₀ T).map (fun T' _ => T')`
      via the round trip `ofK_toK : ofK (toK M) = M`.

* **Syntactic transport**: `Involutory.toK` and `KInvolutory.ofK` carry the
  syntactic involutivity structure across the bridge in both directions
  (the flip of a no-op write-back rule is again a no-op write-back rule).

* **Conjugation closure, machine level** (priorities 2–3):
  `conj_syntacticallyInvolutory_ofK` — for a syntactically involutory `TM0`
  machine `M` and a syntactically reversible `Unit`-indexed pre-machine `R`
  (with inverse `flipM R σR`, by `flipM_tapeSem_inverse`), the collapsed
  conjugate `ofK (seq (seq R (toK M) q0M) (flipM R σR) (σR qfR))` is a
  syntactically involutory `TM0` machine; `conj_tapeSem_ofK` computes its
  tape semantics as the threefold Kleisli composition; and
  `conjugationClosure_tapeSem` packages both in the existential shape of
  `StringConjugationClosure`, at `tapeSem` level.  All three reuse
  `conj_KInvolutory` / `conjSem` from `Symmetrise.lean` — nothing is
  reproved.

* `conj_stringInvolutory_ofK` — with a `StdOutput` hypothesis for the
  collapsed conjugate, its `stringSem` is a partial involution (string
  level).  See the roadmap delta at the end of the file for what still
  separates this from discharging `StringConjugationClosure` itself.
-/
import FiniteOrderTM.InvolutoryString
import FiniteOrderTM.Symmetrise
import FiniteOrderTM.Flip

namespace PeriodicTM

open Turing Turing.TM0

variable {Γ : Type*} [Inhabited Γ] {Λ : Type*} [Inhabited Λ]

/-- `Sum` types inherit inhabitedness from the left summand — needed because
`TM0.Machine` (unlike `KMachine`) demands `Inhabited` state types, and the
conjugate machine lives on `(ΛR ⊕ ΛM) ⊕ ΛR`. -/
scoped instance sumInhabitedLeft {α β : Type*} [Inhabited α] :
    Inhabited (α ⊕ β) := ⟨Sum.inl default⟩

/-! ### Unit-bank plumbing -/

theorem unit_funext {α : Type*} (f : Unit → α) : (fun _ : Unit => f ()) = f :=
  funext fun u => by cases u; rfl

omit [Inhabited Λ] in
theorem KCfg.unit_eta (c : KCfg Γ Λ Unit) :
    (⟨c.q, fun _ => c.tapes ()⟩ : KCfg Γ Λ Unit) = c := by
  obtain ⟨q, U⟩ := c
  exact congrArg (KCfg.mk q) (unit_funext U)

/-- Collapse a `Unit`-bank configuration to a `TM0` configuration. -/
def collapseCfg (c : KCfg Γ Λ Unit) : Cfg Γ Λ := ⟨c.q, c.tapes ()⟩

/-- Expand a `TM0` configuration to a `Unit`-bank configuration. -/
def expandCfg (c : Cfg Γ Λ) : KCfg Γ Λ Unit := ⟨c.q, fun _ => c.Tape⟩

omit [Inhabited Λ] in
@[simp] theorem collapse_expand (c : Cfg Γ Λ) :
    collapseCfg (expandCfg c) = c := rfl

omit [Inhabited Λ] in
@[simp] theorem expand_collapse (c : KCfg Γ Λ Unit) :
    expandCfg (collapseCfg c) = c := KCfg.unit_eta c

/-! ### The two machine translations -/

/-- Embed a `TM0` statement as a `Unit`-bank statement. -/
def toKStmt : Stmt Γ → KStmt Γ Unit
  | Stmt.move d => KStmt.move fun _ => some d
  | Stmt.write b => KStmt.write fun _ => b

/-- Embed a `TM0` machine as a `Unit`-indexed `KMachine`. -/
def toK (M : Machine Γ Λ) : KMachine Γ Λ Unit := fun q a =>
  (M q (a ())).map fun s => (s.1, toKStmt s.2)

/-- Collapse a `Unit`-bank statement to a `TM0` statement.  The scanned
symbol `a` is threaded in so that the two no-op statements (`move` with no
direction, `perm`) become the no-op rule `write a`. -/
def ofKStmt (a : Γ) : KStmt Γ Unit → Stmt Γ
  | KStmt.write b => Stmt.write (b ())
  | KStmt.move d =>
      match d () with
      | some dir => Stmt.move dir
      | none => Stmt.write a
  | KStmt.perm _ => Stmt.write a

/-- Collapse a `Unit`-indexed `KMachine` to a `TM0` machine. -/
def ofK (K : KMachine Γ Λ Unit) : Machine Γ Λ := fun q a =>
  (K q fun _ => a).map fun s => (s.1, ofKStmt a s.2)

omit [Inhabited Γ] in
/-- Round trip: collapsing the embedding gives back the machine. -/
theorem ofK_toK (M : Machine Γ Λ) : ofK (toK M) = M := by
  funext q a
  show ((M q a).map fun s => (s.1, toKStmt s.2)).map
      (fun s => (s.1, ofKStmt a s.2)) = M q a
  rcases e : M q a with - | ⟨q', st⟩
  · rfl
  · rcases st with d | b <;> rfl

/-! ### Step-exact simulation -/

/-- One-step correspondence: `ofK K` on the collapsed configuration performs
exactly the collapsed step of `K`. -/
theorem step_ofK (K : KMachine Γ Λ Unit) (q : Λ) (T : Tape Γ) :
    step (ofK K) ⟨q, T⟩ = (kstep K ⟨q, fun _ => T⟩).map collapseCfg := by
  have hheads : headsV (fun _ : Unit => T) = fun _ => T.1 := rfl
  rcases e : K q (fun _ => T.1) with - | ⟨q', st⟩
  · simp [step, kstep, ofK, hheads, e]
  · rcases st with b | d | π
    · -- write
      simp [step, kstep, ofK, hheads, e, collapseCfg, ofKStmt, KStmt.apply]
    · -- move: split on whether the single bank moves
      rcases hd : d () with - | dir <;>
        simp [step, kstep, ofK, hheads, e, collapseCfg, ofKStmt, hd,
          KStmt.apply, Tape.write_self]
    · -- perm: the unique permutation of `Unit` is a no-op
      simp [step, kstep, ofK, hheads, e, collapseCfg, ofKStmt,
        KStmt.apply, Tape.write_self]

/-- Halting transfers across the collapse. -/
theorem step_ofK_none_iff (K : KMachine Γ Λ Unit) (c : KCfg Γ Λ Unit) :
    step (ofK K) (collapseCfg c) = none ↔ kstep K c = none := by
  have h := step_ofK K c.q (c.tapes ())
  rw [show (⟨c.q, fun _ => c.tapes ()⟩ : KCfg Γ Λ Unit) = c from
    KCfg.unit_eta c] at h
  rw [show collapseCfg c = ⟨c.q, c.tapes ()⟩ from rfl, h]
  rcases kstep K c with - | d <;> simp

theorem reaches_ofK {K : KMachine Γ Λ Unit} {c c' : KCfg Γ Λ Unit}
    (h : StateTransition.Reaches (kstep K) c c') :
    StateTransition.Reaches (step (ofK K)) (collapseCfg c) (collapseCfg c') := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b b' _ hstep ih =>
      refine ih.tail (Option.mem_def.mpr ?_)
      have h := step_ofK K b.q (b.tapes ())
      rw [show (⟨b.q, fun _ => b.tapes ()⟩ : KCfg Γ Λ Unit) = b from
        KCfg.unit_eta b] at h
      rw [show collapseCfg b = ⟨b.q, b.tapes ()⟩ from rfl, h,
        Option.mem_def.mp hstep]
      rfl

theorem reaches_expand_ofK {K : KMachine Γ Λ Unit} {c c' : Cfg Γ Λ}
    (h : StateTransition.Reaches (step (ofK K)) c c') :
    StateTransition.Reaches (kstep K) (expandCfg c) (expandCfg c') := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b b' _ hstep ih =>
      refine ih.tail (Option.mem_def.mpr ?_)
      have h := step_ofK K b.q b.Tape
      rw [Option.mem_def.mp hstep] at h
      rcases e : kstep K (expandCfg b) with - | d
      · rw [show (⟨b.q, fun _ => b.Tape⟩ : KCfg Γ Λ Unit) = expandCfg b
          from rfl, e] at h
        cases h
      · rw [show (⟨b.q, fun _ => b.Tape⟩ : KCfg Γ Λ Unit) = expandCfg b
          from rfl, e, Option.map_some] at h
        have hb' : collapseCfg d = b' := (Option.some.inj h).symm
        rw [show expandCfg b' = d from by rw [← hb', expand_collapse]]

/-! ### The semantics bridge (priority 1) -/

/-- **The KMachine → TM0 semantics bridge**: the collapsed machine computes,
on `T`, exactly the `Unit`-bank semantics of `K` evaluated at the single
bank.  No side hypotheses. -/
theorem tapeSem_ofK (K : KMachine Γ Λ Unit) (q₀ : Λ) (T : Tape Γ) :
    tapeSem (ofK K) q₀ T
      = (ktapeSem K q₀ (fun _ => T)).map (fun U => U ()) := by
  ext T'
  simp only [tapeSem, ktapeSem, Part.mem_map_iff]
  constructor
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨hr, hf⟩ := StateTransition.mem_eval.mp hc
    refine ⟨(expandCfg c).tapes,
      ⟨expandCfg c, StateTransition.mem_eval.mpr ⟨?_, ?_⟩, rfl⟩, rfl⟩
    · exact reaches_expand_ofK hr
    · exact (step_ofK_none_iff K (expandCfg c)).mp
        (by rw [collapse_expand]; exact hf)
  · rintro ⟨U, ⟨d, hd, rfl⟩, rfl⟩
    obtain ⟨hr, hf⟩ := StateTransition.mem_eval.mp hd
    refine ⟨collapseCfg d, StateTransition.mem_eval.mpr ⟨?_, ?_⟩, rfl⟩
    · exact reaches_ofK hr
    · exact (step_ofK_none_iff K d).mpr hf

/-- The same bijection read the other way: the `Unit`-bank semantics of `K`
is the expanded semantics of the collapsed machine. -/
theorem ktapeSem_ofK_expand (K : KMachine Γ Λ Unit) (q₀ : Λ) (T : Tape Γ) :
    ktapeSem K q₀ (fun _ => T)
      = (tapeSem (ofK K) q₀ T).map (fun T' => fun _ => T') := by
  rw [tapeSem_ofK, Part.map_map]
  ext U
  simp only [Part.mem_map_iff, Function.comp]
  constructor
  · intro hU
    exact ⟨U, hU, unit_funext U⟩
  · rintro ⟨V, hV, rfl⟩
    rwa [unit_funext V]

/-- **The TM0 → KMachine semantics bridge**: the embedded machine computes,
on the single bank, exactly the tape semantics of `M`. -/
theorem ktapeSem_toK (M : Machine Γ Λ) (q₀ : Λ) (T : Tape Γ) :
    ktapeSem (toK M) q₀ (fun _ => T)
      = (tapeSem M q₀ T).map (fun T' => fun _ => T') := by
  rw [ktapeSem_ofK_expand, ofK_toK]

/-! ### Syntactic transport of involutivity -/

omit [Inhabited Γ] in
/-- Flip symmetry transports along the embedding. -/
theorem FlipOf.toK {M M' : Machine Γ Λ} {σ : Λ → Λ}
    (h : FlipOf M M' σ) : KFlipOf (toK M) (toK M') σ := by
  have unfold_toK : ∀ (N : Machine Γ Λ) p (a : Unit → Γ),
      PeriodicTM.toK N p a
        = (N p (a ())).map fun s => (s.1, toKStmt s.2) := fun _ _ _ => rfl
  refine ⟨?_, ?_, ?_⟩
  · intro p a q b hrule
    rw [unfold_toK] at hrule
    rcases e : M p (a ()) with - | ⟨q', st⟩
    · rw [e] at hrule; simp at hrule
    · rw [e, Option.map_some] at hrule
      obtain ⟨hq, hst⟩ := Prod.mk.injEq .. ▸ Option.some.inj hrule
      subst hq
      rcases st with d | c
      · simp [toKStmt] at hst
      · obtain rfl : b = fun _ => c := (KStmt.write.inj hst).symm
        have hr := h.flip_write p (a ()) q' c e
        rw [unfold_toK]
        show (M' (σ q') c).map _ = _
        rw [hr]
        simp [toKStmt, unit_funext a]
  · intro p a q d hrule bb
    rw [unfold_toK] at hrule
    rcases e : M p (a ()) with - | ⟨q', st⟩
    · rw [e] at hrule; simp at hrule
    · rw [e, Option.map_some] at hrule
      obtain ⟨hq, hst⟩ := Prod.mk.injEq .. ▸ Option.some.inj hrule
      subst hq
      rcases st with dir | c
      · obtain rfl : d = fun _ => some dir := (KStmt.move.inj hst).symm
        have hr := h.flip_move p (a ()) q' dir e (bb ())
        rw [unfold_toK]
        show (M' (σ q') (bb ())).map _ = _
        rw [hr]
        rfl
      · simp [toKStmt] at hst
  · -- `toK` never produces permutation rules
    intro p a q π hrule bb
    rw [unfold_toK] at hrule
    rcases e : M p (a ()) with - | ⟨q', st⟩
    · rw [e] at hrule; simp at hrule
    · rw [e, Option.map_some] at hrule
      obtain ⟨hq, hst⟩ := Prod.mk.injEq .. ▸ Option.some.inj hrule
      rcases st with d | c <;> simp [toKStmt] at hst

omit [Inhabited Γ] in
/-- Involutivity transports along the embedding. -/
theorem Involutory.toK {M : Machine Γ Λ} {σ : Λ → Λ} {q₀ qf : Λ}
    (h : Involutory M σ q₀ qf) : KInvolutory (PeriodicTM.toK M) σ q₀ qf where
  invol := h.invol
  start := h.start
  halt_iff := fun q a => by
    rw [show (PeriodicTM.toK M q a = none) ↔ (M q (a ()) = none) from by
      rcases e : M q (a ()) with - | s <;> simp [PeriodicTM.toK, e]]
    exact h.halt_iff q (a ())
  flip := h.flip.toK

omit [Inhabited Γ] in
/-- Flip symmetry transports along the collapse: the flip of a collapsed
no-op statement (`move` with no direction, `perm`) is the write-back rule,
whose flip is again a write-back rule. -/
theorem KFlipOf.ofK {K K' : KMachine Γ Λ Unit} {σ : Λ → Λ}
    (h : KFlipOf K K' σ) : FlipOf (ofK K) (ofK K') σ := by
  have unfold_ofK : ∀ (N : KMachine Γ Λ Unit) p (a : Γ),
      PeriodicTM.ofK N p a
        = (N p fun _ => a).map fun s => (s.1, ofKStmt a s.2) :=
    fun _ _ _ => rfl
  refine ⟨?_, ?_⟩
  · -- flip_write
    intro p a q b hrule
    rw [unfold_ofK] at hrule
    rcases e : K p (fun _ => a) with - | ⟨q', st⟩
    · rw [e] at hrule; simp at hrule
    · rw [e, Option.map_some] at hrule
      obtain ⟨hq, hst⟩ := Prod.mk.injEq .. ▸ Option.some.inj hrule
      subst hq
      rcases st with bv | d | π
      · -- genuine write
        obtain rfl : bv () = b := Stmt.write.inj hst
        have hr := h.flip_write p (fun _ => a) q' bv e
        rw [unfold_ofK]
        show (K' (σ q') fun _ => bv ()).map _ = _
        rw [unit_funext bv, hr]
        simp [ofKStmt]
      · rcases hd : d () with - | dir
        · -- no-op move collapses to write-back: b = a
          rw [show ofKStmt a (KStmt.move d) = Stmt.write a from by
            simp [ofKStmt, hd]] at hst
          obtain rfl : a = b := Stmt.write.inj hst
          have hr := h.flip_move p (fun _ => a) q' d e (fun _ => a)
          rw [unfold_ofK]
          show (K' (σ q') fun _ => a).map _ = _
          rw [hr]
          simp [ofKStmt, revMap, hd]
        · -- genuine move never produces a write rule
          rw [show ofKStmt a (KStmt.move d) = Stmt.move dir from by
            simp [ofKStmt, hd]] at hst
          cases hst
      · -- perm collapses to write-back: b = a
        obtain rfl : a = b := Stmt.write.inj hst
        have hr := h.flip_perm p (fun _ => a) q' π e (fun _ => a)
        rw [unfold_ofK]
        show (K' (σ q') fun _ => a).map _ = _
        rw [hr]
        simp [ofKStmt]
  · -- flip_move
    intro p a q dir hrule b
    rw [unfold_ofK] at hrule
    rcases e : K p (fun _ => a) with - | ⟨q', st⟩
    · rw [e] at hrule; simp at hrule
    · rw [e, Option.map_some] at hrule
      obtain ⟨hq, hst⟩ := Prod.mk.injEq .. ▸ Option.some.inj hrule
      subst hq
      rcases st with bv | d | π
      · cases hst
      · rcases hd : d () with - | dir'
        · rw [show ofKStmt a (KStmt.move d) = Stmt.write a from by
            simp [ofKStmt, hd]] at hst
          cases hst
        · rw [show ofKStmt a (KStmt.move d) = Stmt.move dir' from by
            simp [ofKStmt, hd]] at hst
          obtain rfl : dir' = dir := Stmt.move.inj hst
          have hr := h.flip_move p (fun _ => a) q' d e (fun _ => b)
          rw [unfold_ofK]
          show (K' (σ q') fun _ => b).map _ = _
          rw [hr]
          simp [ofKStmt, revMap, hd]
      · cases hst

omit [Inhabited Γ] in
/-- Involutivity transports along the collapse. -/
theorem KInvolutory.ofK {K : KMachine Γ Λ Unit} {σ : Λ → Λ} {q₀ qf : Λ}
    (h : KInvolutory K σ q₀ qf) : Involutory (PeriodicTM.ofK K) σ q₀ qf where
  invol := h.invol
  start := h.start
  halt_iff := fun q a => by
    rw [show (PeriodicTM.ofK K q a = none) ↔ (K q (fun _ => a) = none) from by
      rcases e : K q (fun _ => a) with - | s <;> simp [PeriodicTM.ofK, e]]
    exact h.halt_iff q (fun _ => a)
  flip := h.flip.ofK

/-! ### Conjugation closure at machine level (priorities 2–3) -/

variable {ΛR ΛM : Type*}

/-- **Machine-level conjugation closure, syntactic form**: collapsing the
`Unit`-bank conjugate of an embedded syntactically involutory `TM0` machine
`M` by a syntactically reversible pre-machine `R` yields a *syntactically
involutory `TM0` machine*.  This is `conj_KInvolutory` (Symmetrise.lean)
transported across the bridge — the composite-machine syntactic
involutivity demanded by roadmap step 3, at `TM0` level. -/
theorem conj_syntacticallyInvolutory_ofK [Inhabited ΛR] [Inhabited ΛM]
    {R : KMachine Γ ΛR Unit} {M : Machine Γ ΛM}
    {σR : ΛR → ΛR} {σM : ΛM → ΛM} {q0R qfR : ΛR} {q0M qfM : ΛM}
    (hM : Involutory M σM q0M qfM)
    (hσR : ∀ q, σR (σR q) = q) (hRrev : KReversible R)
    (hRhalt : ∀ q a, R q a = none ↔ q = qfR)
    (hRent : ∀ q b, (∃ v, Demand R q b v) ↔ q ≠ q0R) :
    SyntacticallyInvolutory
      (ofK (seq (seq R (toK M) q0M) (flipM R σR) (σR qfR)))
      (Sum.inl (Sum.inl q0R)) (Sum.inr (σR q0R)) :=
  ⟨conjσ σR σM,
    (conj_KInvolutory hM.toK hσR hRrev hRhalt hRent).ofK⟩

/-- **Machine-level conjugation closure, semantic form**: the collapsed
conjugate computes exactly the threefold Kleisli composition
`⟦flipM R⟧ ∘ ⟦M⟧ ∘ ⟦R⟧` at tape level (`conjSem` transported across the
bridge; no side hypotheses). -/
theorem conj_tapeSem_ofK [Inhabited ΛR] [Inhabited ΛM]
    (R : KMachine Γ ΛR Unit) (M : Machine Γ ΛM) (σR : ΛR → ΛR)
    (q0R : ΛR) (q0M : ΛM) (qfR : ΛR) (T : Tape Γ) :
    tapeSem (ofK (seq (seq R (toK M) q0M) (flipM R σR) (σR qfR)))
        (Sum.inl (Sum.inl q0R)) T
      = ((ktapeSem R q0R (fun _ => T)).map (fun U => U ())).bind fun u =>
          (tapeSem M q0M u).bind fun v =>
            (ktapeSem (flipM R σR) (σR qfR) (fun _ => v)).map fun U =>
              U () := by
  rw [tapeSem_ofK, conjSem]
  ext t
  simp only [Part.mem_map_iff, Part.mem_bind_iff]
  constructor
  · rintro ⟨W, ⟨V, ⟨U, hU, hV⟩, hW⟩, rfl⟩
    rw [← unit_funext U, ktapeSem_toK, Part.mem_map_iff] at hV
    obtain ⟨v, hv, hVv⟩ := hV
    refine ⟨U (), ⟨U, hU, rfl⟩, v, hv, ?_⟩
    rw [← hVv] at hW
    exact ⟨W, hW, rfl⟩
  · rintro ⟨u, ⟨U, hU, rfl⟩, v, hv, W, hW, rfl⟩
    refine ⟨W, ⟨fun _ => v, ⟨U, hU, ?_⟩, hW⟩, rfl⟩
    rw [← unit_funext U, ktapeSem_toK, Part.mem_map_iff]
    exact ⟨v, hv, rfl⟩

/-- **Conjugation closure packaged** in the existential shape of
`StringConjugationClosure`, at `tapeSem` level: from a syntactically
involutory `M` and a syntactically reversible pre-machine `R` there exists a
syntactically involutory `TM0` machine computing the conjugation of `⟦M⟧` by
`⟦R⟧` (post-machine `flipM R σR`, the inverse of `R` by
`flipM_tapeSem_inverse`). -/
theorem conjugationClosure_tapeSem (Γ ΛR ΛM : Type) [Inhabited Γ]
    [Inhabited ΛR] [Inhabited ΛM]
    (R : KMachine Γ ΛR Unit) (M : Machine Γ ΛM)
    (σR : ΛR → ΛR) (σM : ΛM → ΛM) (q0R qfR : ΛR) (q0M qfM : ΛM)
    (hM : Involutory M σM q0M qfM)
    (hσR : ∀ q, σR (σR q) = q) (hRrev : KReversible R)
    (hRhalt : ∀ q a, R q a = none ↔ q = qfR)
    (hRent : ∀ q b, (∃ v, Demand R q b v) ↔ q ≠ q0R) :
    ∃ (Λ' : Type) (_ : Inhabited Λ') (D : Machine Γ Λ') (d₀ df : Λ'),
      SyntacticallyInvolutory D d₀ df ∧
      ∀ T, tapeSem D d₀ T
        = ((ktapeSem R q0R (fun _ => T)).map (fun U => U ())).bind fun u =>
            (tapeSem M q0M u).bind fun v =>
              (ktapeSem (flipM R σR) (σR qfR) (fun _ => v)).map fun U =>
                U () :=
  ⟨(ΛR ⊕ ΛM) ⊕ ΛR, inferInstance,
    ofK (seq (seq R (toK M) q0M) (flipM R σR) (σR qfR)),
    Sum.inl (Sum.inl q0R), Sum.inr (σR q0R),
    conj_syntacticallyInvolutory_ofK hM hσR hRrev hRhalt hRent,
    fun T => conj_tapeSem_ofK R M σR q0R q0M qfR T⟩

/-- **String level**: with a `StdOutput` hypothesis for the collapsed
conjugate, its string semantics is a partial involution.  This is the
string-level half of `StringConjugationClosure` for this class of
conjugators; the `StdOutput` obligation itself is roadmap step 3 territory
(a property of Nakano's symmetrisation construction). -/
theorem conj_stringInvolutory_ofK [Inhabited ΛR] [Inhabited ΛM]
    {R : KMachine Γ ΛR Unit} {M : Machine Γ ΛM}
    {σR : ΛR → ΛR} {σM : ΛM → ΛM} {q0R qfR : ΛR} {q0M qfM : ΛM}
    (hM : Involutory M σM q0M qfM)
    (hσR : ∀ q, σR (σR q) = q) (hRrev : KReversible R)
    (hRhalt : ∀ q a, R q a = none ↔ q = qfR)
    (hRent : ∀ q b, (∃ v, Demand R q b v) ↔ q ≠ q0R)
    (hSO : StdOutput (ofK (seq (seq R (toK M) q0M) (flipM R σR) (σR qfR)))
      (Sum.inl (Sum.inl q0R))) :
    StringInvolutory
      (ofK (seq (seq R (toK M) q0M) (flipM R σR) (σR qfR)))
      (Sum.inl (Sum.inl q0R)) :=
  (conj_syntacticallyInvolutory_ofK hM hσR hRrev hRhalt hRent).stringInvolutory
    hSO

/-!
### Roadmap delta (step 2: KMachine ↔ TM0 transport)

**Done here:**
* The full bridge for `Unit`-indexed KMachines (`toK` / `ofK`), step-exact
  in both directions, with the semantics equations `tapeSem_ofK`,
  `ktapeSem_ofK_expand`, `ktapeSem_toK`, and the round trip `ofK_toK`.
  This is *stronger* than a `k = 1` correspondence "up to simulation":
  the two models are literally step-bisimilar, so nothing semantic is
  lost in transport.
* Syntactic transport in both directions (`Involutory.toK`,
  `KInvolutory.ofK`, via `FlipOf.toK` / `KFlipOf.ofK`) — the delicate
  point being that the collapse turns no-op `move`/`perm` rules into
  write-back rules, whose flips are again write-back rules.
* Machine-level conjugation closure at `TM0`/`tapeSem`
  (`conj_syntacticallyInvolutory_ofK`, `conj_tapeSem_ofK`,
  `conjugationClosure_tapeSem`), reusing `conj_KInvolutory`/`conjSem`
  from `Symmetrise.lean` unchanged.  The composite-machine *syntactic*
  involutivity of roadmap step 3 is therefore proved, not just stated,
  for this class of composites.
* The string-level partial-involution consequence
  (`conj_stringInvolutory_ofK`) under a `StdOutput` hypothesis.

**Remaining for `StringConjugationClosure` itself:**
* Its hypotheses give the conjugator `R` as a `TM0` machine with only a
  *semantic* inverse at `stringSem`.  Closing the gap needs either
  (i) a reversibilisation step producing, from such an `R`, a
  syntactically reversible machine (`KReversible` + halt/entry
  discipline) computing the same string function — this is exactly
  Bennett/Lecerf material, roadmap step 3's history construction; or
  (ii) a weakening of `StringConjugationClosure` to syntactic hypotheses
  on `R`, at which point `conjugationClosure_tapeSem` + a `StdOutput`
  argument discharge it.
* `StdOutput` for the composite: the conjugate returns the head wherever
  `flipM R` leaves it, so standard output must be arranged by the
  symmetrisation construction (flagged in `IOConvention.lean`), then the
  `stringSem` equation follows from `conj_tapeSem_ofK` by reading
  `s.length` symbols.
* Multi-bank conjugators (`k > 1`): the present transport is exact for
  one bank; the 2k-tape construction of step 3 will instead need
  `Lift`/`Reindex` plus an encoding of the hidden banks, replacing
  equality of semantics by agreement on encoded inputs
  (`StringCompletenessGoal`).
-/

end PeriodicTM
