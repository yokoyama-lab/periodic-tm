/-
FiniteOrderTM/MultiTape.lean

Track B, milestones M1–M2: a k-tape Turing machine model with Nakano-style
*permutation rules*, and the port of the flip/soundness theory from
`Machine.lean`.

A rule of a `KMachine` reads the full head vector and performs one of
* `write b⃗` — overwrite every head (so the head vector after the step is
  exactly `b⃗`, mirroring the single-tape write case),
* `move d⃗`  — shift a selected subset of tapes (`d⃗ : ι → Option Dir`),
* `perm π`  — permute the tape banks (tape `j` moves to position `π j`).

Reversal swaps the roles: the flip of `write a⃗ ↦ b⃗` writes `a⃗` back, the
flip of `move d⃗` moves by the reversed directions, and the flip of
`perm π` is `perm π⁻¹`.  In the *self*-flipped (involutory) case
determinism forces `π⁻¹ = π` — Nakano's third condition, "every
permutation rule is involutory", is thereby *derived* rather than
postulated; `involutory_bankSwap` below shows the smallest instance.

As in the single-tape case, none of the reversal theorems assume
reversibility of `M`: flip symmetry of the rule set alone reverses runs.

Remaining Track B milestones (M3–M7): sequential composition combinators,
tape-bank lifting `k → 2k`, `flip M` as an object, Nakano's symmetrisation
(Lemmas 4.4–4.5), and machine-level completeness.
-/
import FiniteOrderTM.Machine

namespace PeriodicTM

open Turing

variable {Γ : Type*} [Inhabited Γ]
variable {Λ : Type*} [Inhabited Λ]
variable {Λ' : Type*}
variable {ι : Type*}

/-! ### The k-tape model -/

/-- One statement of a k-tape machine. -/
inductive KStmt (Γ : Type*) (ι : Type*)
  | write (b : ι → Γ)
  | move (d : ι → Option Dir)
  | perm (π : Equiv.Perm (ι))

/-- A k-tape machine: read the state and the full head vector, optionally
produce a next state and a statement. -/
abbrev KMachine (Γ : Type*) (Λ : Type*) (ι : Type*) :=
  Λ → (ι → Γ) → Option (Λ × KStmt Γ ι)

/-- A k-tape configuration. -/
structure KCfg (Γ : Type*) [Inhabited Γ] (Λ : Type*) (ι : Type*) where
  q : Λ
  tapes : ι → Tape Γ

/-- The current head vector of a tape bank. -/
def headsV (T : ι → Tape Γ) : ι → Γ := fun i => (T i).1

/-- Apply a statement to a tape bank. -/
def KStmt.apply : KStmt Γ ι → (ι → Tape Γ) → (ι → Tape Γ)
  | KStmt.write b, T => fun i => (T i).write (b i)
  | KStmt.move d, T => fun i =>
      match d i with
      | none => T i
      | some dir => (T i).move dir
  | KStmt.perm π, T => fun i => T (π⁻¹ i)

/-- Execution semantics. -/
def kstep (M : KMachine Γ Λ ι) : KCfg Γ Λ ι → Option (KCfg Γ Λ ι) :=
  fun c => (M c.q (headsV c.tapes)).map fun s => ⟨s.1, s.2.apply c.tapes⟩

/-- Reversal of a direction vector. -/
def revMap (d : ι → Option Dir) : ι → Option Dir :=
  fun i => (d i).map dirRev

/-! ### Cancellation lemmas for the three statement kinds -/

@[simp] theorem headsV_write (T : ι → Tape Γ) (b : ι → Γ) :
    headsV ((KStmt.write b).apply T) = b := rfl

theorem write_write_cancel (T : ι → Tape Γ) (b : ι → Γ) :
    (KStmt.write (headsV T)).apply ((KStmt.write b).apply T) = T := by
  funext i
  show (((T i).write (b i)).write ((T i).1)) = T i
  rw [tape_write_write, Tape.write_self]

theorem move_cancel (T : ι → Tape Γ) (d : ι → Option Dir) :
    (KStmt.move (revMap d)).apply ((KStmt.move d).apply T) = T := by
  funext i
  show (KStmt.move (revMap d)).apply ((KStmt.move d).apply T) i = T i
  rcases h : d i with - | dir <;>
    simp [KStmt.apply, revMap, h]

theorem perm_cancel (T : ι → Tape Γ) (π : Equiv.Perm (ι)) :
    (KStmt.perm π⁻¹).apply ((KStmt.perm π).apply T) = T := by
  funext i
  simp [KStmt.apply]

/-! ### Flips and reversal -/

/-- Mirror of a k-tape configuration (state map may change the state type). -/
def kmirror (σ : Λ → Λ') (c : KCfg Γ Λ ι) : KCfg Γ Λ' ι := ⟨σ c.q, c.tapes⟩

/-- `KFlipOf M M' σ`: every rule of `M` has its time-reversed image in `M'`.
The flip of a permutation rule is the rule for the *inverse* permutation.
The state map `σ : Λ → Λ'` may be heterogeneous; the relational reversal
theorems below never use `σ ∘ σ = id`. -/
structure KFlipOf (M : KMachine Γ Λ ι) (M' : KMachine Γ Λ' ι) (σ : Λ → Λ') :
    Prop where
  flip_write : ∀ p a q b, M p a = some (q, KStmt.write b) →
    M' (σ q) b = some (σ p, KStmt.write a)
  flip_move : ∀ p a q d, M p a = some (q, KStmt.move d) →
    ∀ b, M' (σ q) b = some (σ p, KStmt.move (revMap d))
  flip_perm : ∀ p a q π, M p a = some (q, KStmt.perm π) →
    ∀ b, M' (σ q) b = some (σ p, KStmt.perm π⁻¹)

namespace KFlipOf

variable {M : KMachine Γ Λ ι} {M' : KMachine Γ Λ' ι} {σ : Λ → Λ'}

omit [Inhabited Λ] in
/-- One-step reversal for k-tape machines. -/
theorem step_rev (h : KFlipOf M M' σ) {c c' : KCfg Γ Λ ι}
    (hs : kstep M c = some c') :
    kstep M' (kmirror σ c') = some (kmirror σ c) := by
  obtain ⟨p, T⟩ := c
  rcases e : M p (headsV T) with - | ⟨q, s⟩
  · simp [kstep, e] at hs
  rcases s with b | d | π
  · -- write rule
    have hc' : (⟨q, (KStmt.write b).apply T⟩ : KCfg Γ Λ ι) = c' := by
      simpa [kstep, e] using hs
    subst hc'
    have hr := h.flip_write p (headsV T) q b e
    simp [kstep, kmirror, headsV_write, hr, write_write_cancel]
  · -- move rule
    have hc' : (⟨q, (KStmt.move d).apply T⟩ : KCfg Γ Λ ι) = c' := by
      simpa [kstep, e] using hs
    subst hc'
    have hr := h.flip_move p (headsV T) q d e
      (headsV ((KStmt.move d).apply T))
    simp [kstep, kmirror, hr, move_cancel]
  · -- permutation rule
    have hc' : (⟨q, (KStmt.perm π).apply T⟩ : KCfg Γ Λ ι) = c' := by
      simpa [kstep, e] using hs
    subst hc'
    have hr := h.flip_perm p (headsV T) q π e
      (headsV ((KStmt.perm π).apply T))
    simp [kstep, kmirror, hr, perm_cancel]

omit [Inhabited Λ] in
/-- Run reversal. -/
theorem reaches_rev (h : KFlipOf M M' σ) {c c' : KCfg Γ Λ ι}
    (hr : StateTransition.Reaches (kstep M) c c') :
    StateTransition.Reaches (kstep M') (kmirror σ c') (kmirror σ c) := by
  induction hr with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact Relation.ReflTransGen.head
        (Option.mem_def.mpr (h.step_rev (Option.mem_def.mp hstep))) ih

omit [Inhabited Λ] in
/-- Lecerf reversal at evaluation level, k-tape version. -/
theorem eval_rev (h : KFlipOf M M' σ) {q₀ qf : Λ}
    (h0 : ∀ a, M' (σ q₀) a = none) {T T' : ι → Tape Γ}
    (he : (⟨qf, T'⟩ : KCfg Γ Λ ι) ∈ StateTransition.eval (kstep M) ⟨q₀, T⟩) :
    (⟨σ q₀, T⟩ : KCfg Γ Λ' ι) ∈ StateTransition.eval (kstep M') ⟨σ qf, T'⟩ := by
  obtain ⟨hr, -⟩ := StateTransition.mem_eval.mp he
  refine StateTransition.mem_eval.mpr ⟨?_, ?_⟩
  · simpa [kmirror] using h.reaches_rev hr
  · simp [kstep, h0]

end KFlipOf

omit [Inhabited Λ] in
/-- Any halting configuration of a machine halting exactly at `h` is at `h`. -/
theorem keval_halt_state {M : KMachine Γ Λ ι} {h : Λ}
    (hh : ∀ q a, M q a = none ↔ q = h) {c c' : KCfg Γ Λ ι}
    (he : c' ∈ StateTransition.eval (kstep M) c) : c'.q = h := by
  obtain ⟨-, hhalt⟩ := StateTransition.mem_eval.mp he
  obtain ⟨q, T⟩ := c'
  rcases e : M q (headsV T) with - | s
  · exact (hh q (headsV T)).mp e
  · simp [kstep, e] at hhalt

/-- Tape-bank semantics: initial bank to final bank, if the machine halts. -/
def ktapeSem (M : KMachine Γ Λ ι) (q₀ : Λ) (T : ι → Tape Γ) :
    Part (ι → Tape Γ) :=
  (StateTransition.eval (kstep M) ⟨q₀, T⟩).map KCfg.tapes

omit [Inhabited Λ] in
/-- Inverse semantics for mutual flips, k-tape version. -/
theorem ktapeSem_inverse {M M' : KMachine Γ Λ ι} {σ : Λ → Λ} {q₀ qf : Λ}
    (hσ : ∀ q, σ (σ q) = q)
    (hfwd : KFlipOf M M' σ) (hbwd : KFlipOf M' M σ)
    (hM : ∀ q a, M q a = none ↔ q = qf)
    (hM' : ∀ q a, M' q a = none ↔ q = σ q₀)
    {T T' : ι → Tape Γ} :
    T' ∈ ktapeSem M q₀ T ↔ T ∈ ktapeSem M' (σ qf) T' := by
  constructor
  · intro hT'
    obtain ⟨c, hc, rfl⟩ := (Part.mem_map_iff _).mp hT'
    have hq : c.q = qf := keval_halt_state hM hc
    have hc' : (⟨qf, c.tapes⟩ : KCfg Γ Λ ι) ∈
        StateTransition.eval (kstep M) ⟨q₀, T⟩ := by
      rw [← hq]; exact hc
    have h0 : ∀ a, M' (σ q₀) a = none := fun a => (hM' (σ q₀) a).mpr rfl
    exact (Part.mem_map_iff _).mpr ⟨⟨σ q₀, T⟩, hfwd.eval_rev h0 hc', rfl⟩
  · intro hT
    obtain ⟨c, hc, rfl⟩ := (Part.mem_map_iff _).mp hT
    have hq : c.q = σ q₀ := keval_halt_state hM' hc
    have hc' : (⟨σ q₀, c.tapes⟩ : KCfg Γ Λ ι) ∈
        StateTransition.eval (kstep M') ⟨σ qf, T'⟩ := by
      rw [← hq]; exact hc
    have h0 : ∀ a, M (σ (σ qf)) a = none := fun a => by
      rw [hσ qf]; exact (hM qf a).mpr rfl
    have := hbwd.eval_rev h0 hc'
    rw [hσ, hσ] at this
    exact (Part.mem_map_iff _).mpr ⟨⟨qf, T'⟩, this, rfl⟩

/-- An involutory k-tape machine: self-flipped under an involutive state map
exchanging start and halt states. -/
structure KInvolutory (M : KMachine Γ Λ ι) (σ : Λ → Λ) (q₀ qf : Λ) : Prop where
  invol : ∀ q, σ (σ q) = q
  start : σ q₀ = qf
  halt_iff : ∀ q a, M q a = none ↔ q = qf
  flip : KFlipOf M M σ

namespace KInvolutory

variable {M : KMachine Γ Λ ι} {σ : Λ → Λ} {q₀ qf : Λ}

omit [Inhabited Λ] in
theorem eval_symm (h : KInvolutory M σ q₀ qf) {T T' : ι → Tape Γ}
    (he : (⟨qf, T'⟩ : KCfg Γ Λ ι) ∈ StateTransition.eval (kstep M) ⟨q₀, T⟩) :
    (⟨qf, T⟩ : KCfg Γ Λ ι) ∈ StateTransition.eval (kstep M) ⟨q₀, T'⟩ := by
  have hqf : σ qf = q₀ := by
    conv_lhs => rw [← h.start]
    exact h.invol q₀
  have h0 : ∀ a, M (σ q₀) a = none := fun a => by
    rw [h.start]; exact (h.halt_iff qf a).mpr rfl
  have := h.flip.eval_rev h0 he
  rwa [h.start, hqf] at this

omit [Inhabited Λ] in
/-- **k-tape machine-level soundness**: an involutory k-tape machine — now
including Nakano-style permutation rules — computes a partial involution on
tape banks. -/
theorem ktapeSem_involutive (h : KInvolutory M σ q₀ qf)
    {T T' : ι → Tape Γ} (hT' : T' ∈ ktapeSem M q₀ T) :
    T ∈ ktapeSem M q₀ T' := by
  obtain ⟨c, hc, rfl⟩ := (Part.mem_map_iff _).mp hT'
  have hq : c.q = qf := keval_halt_state h.halt_iff hc
  have hc' : (⟨qf, c.tapes⟩ : KCfg Γ Λ ι) ∈
      StateTransition.eval (kstep M) ⟨q₀, T⟩ := by
    rw [← hq]; exact hc
  exact (Part.mem_map_iff _).mpr ⟨⟨qf, T⟩, h.eval_symm hc', rfl⟩

end KInvolutory

section Sanity

/-- The two-state machine that permutes the tape banks by `π` and halts. -/
def bankSwap (π : Equiv.Perm (ι)) : KMachine Γ Bool ι := fun q _ =>
  match q with
  | true => none
  | false => some (true, KStmt.perm π)

/-- Conversely, if `bankSwap π` is involutory then `π` is self-inverse:
its permutation rule is its own flip partner, so determinism forces
`π⁻¹ = π`.  This is special to self-paired rules — `involutory_chain`
below exhibits an involutory machine whose permutation rules are *not*
involutory, so Nakano's third condition is independent in general. -/
theorem self_inverse_of_involutory_bankSwap {π : Equiv.Perm ι}
    (h : KInvolutory (Γ := Γ) (bankSwap π) not false true) : π⁻¹ = π := by
  have hr := h.flip.flip_perm false (fun _ => default) true π
    (by simp [bankSwap]) (fun _ => default)
  have h' : π = π⁻¹ := by simpa [bankSwap] using hr
  exact h'.symm

omit [Inhabited Γ] in
/-- `bankSwap π` is involutory precisely when `π` is self-inverse — Nakano's
"every permutation rule is involutory" materialising as a consistency
condition of the self-flip. -/
theorem involutory_bankSwap (π : Equiv.Perm (ι)) (hπ : π⁻¹ = π) :
    KInvolutory (Γ := Γ) (bankSwap π) not false true where
  invol := Bool.not_not
  start := rfl
  halt_iff := by intro q a; cases q <;> simp [bankSwap]
  flip := by
    refine ⟨?_, ?_, ?_⟩
    · intro p a q b hpq
      cases p <;> simp [bankSwap] at hpq
    · intro p a q d hpq
      cases p <;> simp [bankSwap] at hpq
    · intro p a q π' hpq
      cases p <;> simp [bankSwap] at hpq ⊢
      obtain ⟨rfl, rfl⟩ := hpq
      simp [hπ]

/-! #### Independence of the third condition

For permutation rules that are *not* their own flip partners, involutivity
of the permutation is NOT forced: the four-state chain
`perm π ; write-back ; perm π⁻¹` is involutory for *every* `π`.  So
Nakano's third condition is genuinely independent in general; it is
derived only for self-paired rules such as `bankSwap`'s. -/

/-- Four states for the chain machine. -/
inductive Four | a | b | c | d

instance : Inhabited Four := ⟨Four.a⟩

/-- The state involution pairing the two ends and the two middles. -/
def σ₄ : Four → Four
  | Four.a => Four.d
  | Four.b => Four.c
  | Four.c => Four.b
  | Four.d => Four.a

/-- `perm π`, then write back the heads (a no-op), then `perm π⁻¹`. -/
def chain (π : Equiv.Perm ι) : KMachine Γ Four ι := fun s v =>
  match s with
  | Four.a => some (Four.b, KStmt.perm π)
  | Four.b => some (Four.c, KStmt.write v)
  | Four.c => some (Four.d, KStmt.perm π⁻¹)
  | Four.d => none

omit [Inhabited Γ] in
/-- The chain is involutory for **every** `π` — including permutations of
order three or more.  Its two permutation rules are flip partners of each
other, not of themselves, so determinism never forces `π⁻¹ = π`. -/
theorem involutory_chain (π : Equiv.Perm ι) :
    KInvolutory (Γ := Γ) (chain π) σ₄ Four.a Four.d where
  invol := by intro q; cases q <;> rfl
  start := rfl
  halt_iff := by intro q v; cases q <;> simp [chain]
  flip := by
    refine ⟨?_, ?_, ?_⟩
    · -- write rules: only `Four.b`, which is self-paired and writes back
      intro p v q b hpq
      cases p <;> simp [chain] at hpq
      obtain ⟨rfl, rfl⟩ := hpq
      simp [chain, σ₄]
    · -- no move rules
      intro p v q d hpq
      cases p <;> simp [chain] at hpq
    · -- the two perm rules are each other's flips
      intro p v q π' hpq
      cases p <;> simp [chain] at hpq <;>
        obtain ⟨rfl, rfl⟩ := hpq <;> intro b <;> simp [chain, σ₄]

/-- A concrete non-self-inverse permutation (a 3-cycle), witnessing that
`involutory_chain` genuinely covers non-involutory permutation rules. -/
example : (finRotate 3)⁻¹ ≠ finRotate 3 := by decide

end Sanity

end PeriodicTM
