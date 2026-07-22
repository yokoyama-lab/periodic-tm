/-
FiniteOrderTM/Machine.lean

Machine-level theory of involutory Turing machines on mathlib's `Turing.TM0`
model, covering the single-tape kernels of both halves of Nakano's theorems:

* **Soundness** (Thm 4.2 kernel): a machine whose rule set is flip-symmetric
  under an involutive state map computes a partial involution
  (`Involutory.tapeSem_involutive`).

* **Completeness direction** (Thm 4.6 kernel): the engine of the completeness
  construction is *Lecerf reversal* — a machine `M'` whose rules are the
  flips of `M`'s computes the inverse partial function.  This is mechanised
  relationally: `FlipOf M M' σ` says every `M`-rule has its reversed image in
  `M'`, and

  - `FlipOf.eval_rev` reverses whole runs (`⟦M'⟧ ⊇ ⟦M⟧⁻¹`),
  - `tapeSem_inverse` upgrades this to `⟦M'⟧ = ⟦M⟧⁻¹` for mutual flips,
  - `tapeSem_involutive_of_flip_equiv` is the bridge: a machine semantically
    equal to its own reversal computes a partial involution.

  Nakano's full completeness additionally *symmetrises* a reversible machine
  so that flip-equality holds syntactically; that construction lives on
  `2k` tapes (tape-bank permutations) and needs a multi-tape model, so it is
  out of scope for `TM0` and left as the main remaining formalisation target.

`TM0` is a good host because each step either writes or moves (never both),
matching the quadruple discipline of reversible TMs, so each rule type has a
clean reversal:

* write rule  `(p, a) ↦ (q, write b)`   reverses to  `(σ q, b) ↦ (σ p, write a)`;
* move rule   `(p, ·) ↦ (q, move d)`    reverses to  `(σ q, ·) ↦ (σ p, move d.rev)`.

Notably, *none of the reversal theorems assume reversibility* of `M`: flip
symmetry of the rule set alone reverses every run.  (Backward determinism is
what makes the flipped rule set a deterministic machine in the first place
when one tries to construct `M'` from `M`; here `M'` is given, so even that
is not needed.)
-/
import Mathlib

namespace PeriodicTM

open Turing Turing.TM0

variable {Γ : Type*} [Inhabited Γ]
variable {Λ : Type*} [Inhabited Λ]

/-- Reversal of a head direction. -/
def dirRev : Dir → Dir
  | Dir.left => Dir.right
  | Dir.right => Dir.left

@[simp] theorem tape_move_dirRev (T : Tape Γ) (d : Dir) :
    (T.move d).move (dirRev d) = T := by
  cases d <;> simp [dirRev]

@[simp] theorem tape_write_write (T : Tape Γ) (a b : Γ) :
    (T.write b).write a = T.write a := rfl

/-- Mirror of a configuration: apply `σ` to the state, keep the tape. -/
def mirror (σ : Λ → Λ) (c : Cfg Γ Λ) : Cfg Γ Λ := ⟨σ c.q, c.Tape⟩

/-- `FlipOf M M' σ`: every rule of `M` has its time-reversed image (under the
state map `σ`) among the rules of `M'`.  With `M' = M` this is Nakano's flip
symmetry; with `M' ≠ M` it is the relational form of "`M'` is a reversal of
`M`" (Lecerf). -/
structure FlipOf (M M' : Machine Γ Λ) (σ : Λ → Λ) : Prop where
  flip_write : ∀ p a q b, M p a = some (q, Stmt.write b) →
    M' (σ q) b = some (σ p, Stmt.write a)
  flip_move : ∀ p a q d, M p a = some (q, Stmt.move d) →
    ∀ b, M' (σ q) b = some (σ p, Stmt.move (dirRev d))

namespace FlipOf

variable {M M' : Machine Γ Λ} {σ : Λ → Λ}

/-- **One-step reversal.**  A forward step `c → c'` of `M` yields the
backward step `mirror c' → mirror c` of `M'`. -/
theorem step_rev (h : FlipOf M M' σ) {c c' : Cfg Γ Λ}
    (hs : step M c = some c') : step M' (mirror σ c') = some (mirror σ c) := by
  obtain ⟨p, T⟩ := c
  rcases e : M p T.1 with - | ⟨q, s⟩
  · simp [step, e] at hs
  rcases s with d | b
  · -- move rule
    have hc' : (⟨q, T.move d⟩ : Cfg Γ Λ) = c' := by
      simpa [step, e] using hs
    subst hc'
    have hr := h.flip_move p T.1 q d e ((T.move d).1)
    simp [step, mirror, hr]
  · -- write rule
    have hc' : (⟨q, T.write b⟩ : Cfg Γ Λ) = c' := by
      simpa [step, e] using hs
    subst hc'
    have hr := h.flip_write p T.1 q b e
    have hhead : (T.write b).1 = b := rfl
    simp [step, mirror, hhead, hr]

/-- **Run reversal**: a multi-step run of `M` reverses to a run of `M'`
between the mirrored configurations. -/
theorem reaches_rev (h : FlipOf M M' σ) {c c' : Cfg Γ Λ}
    (hr : StateTransition.Reaches (step M) c c') :
    StateTransition.Reaches (step M') (mirror σ c') (mirror σ c) := by
  induction hr with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact Relation.ReflTransGen.head
        (Option.mem_def.mpr (h.step_rev (Option.mem_def.mp hstep))) ih

/-- **Lecerf reversal at evaluation level**: if `M`, started at `q₀` on tape
`T`, halts at `qf` with tape `T'`, then `M'`, started at `σ qf` on `T'`,
halts at `σ q₀` with `T`.  Note the minimal hypotheses: no involutivity of
`σ`, no reversibility of `M` — only that `σ q₀` is halting for `M'`. -/
theorem eval_rev (h : FlipOf M M' σ) {q₀ qf : Λ}
    (h0 : ∀ a, M' (σ q₀) a = none) {T T' : Tape Γ}
    (he : (⟨qf, T'⟩ : Cfg Γ Λ) ∈ StateTransition.eval (step M) ⟨q₀, T⟩) :
    (⟨σ q₀, T⟩ : Cfg Γ Λ) ∈ StateTransition.eval (step M') ⟨σ qf, T'⟩ := by
  obtain ⟨hr, -⟩ := StateTransition.mem_eval.mp he
  refine StateTransition.mem_eval.mpr ⟨?_, ?_⟩
  · simpa [mirror] using h.reaches_rev hr
  · simp [step, h0]

end FlipOf

/-- Any halting configuration of a machine that halts exactly at `h` is
at `h`. -/
theorem eval_halt_state {M : Machine Γ Λ} {h : Λ}
    (hh : ∀ q a, M q a = none ↔ q = h) {c c' : Cfg Γ Λ}
    (he : c' ∈ StateTransition.eval (step M) c) : c'.q = h := by
  obtain ⟨-, hhalt⟩ := StateTransition.mem_eval.mp he
  obtain ⟨q, T⟩ := c'
  rcases e : M q T.1 with - | s
  · exact (hh q T.1).mp e
  · simp [step, e] at hhalt

/-- Tape-level semantics: the partial map sending an initial tape to the
final tape, if the machine halts. -/
def tapeSem (M : Machine Γ Λ) (q₀ : Λ) (T : Tape Γ) : Part (Tape Γ) :=
  (StateTransition.eval (step M) ⟨q₀, T⟩).map Cfg.Tape

/-- **Inverse semantics for mutual flips**: if `M` and `M'` are flips of one
another under an involutive `σ`, `M` halts exactly at `qf` and `M'` exactly
at `σ q₀`, then `M'` (started at `σ qf`) computes precisely the inverse
partial function of `M` (started at `q₀`). -/
theorem tapeSem_inverse {M M' : Machine Γ Λ} {σ : Λ → Λ} {q₀ qf : Λ}
    (hσ : ∀ q, σ (σ q) = q)
    (hfwd : FlipOf M M' σ) (hbwd : FlipOf M' M σ)
    (hM : ∀ q a, M q a = none ↔ q = qf)
    (hM' : ∀ q a, M' q a = none ↔ q = σ q₀)
    {T T' : Tape Γ} :
    T' ∈ tapeSem M q₀ T ↔ T ∈ tapeSem M' (σ qf) T' := by
  constructor
  · intro hT'
    obtain ⟨c, hc, rfl⟩ := (Part.mem_map_iff _).mp hT'
    have hq : c.q = qf := eval_halt_state hM hc
    have hc' : (⟨qf, c.Tape⟩ : Cfg Γ Λ) ∈
        StateTransition.eval (step M) ⟨q₀, T⟩ := by
      rw [← hq]; exact hc
    have h0 : ∀ a, M' (σ q₀) a = none := fun a => (hM' (σ q₀) a).mpr rfl
    exact (Part.mem_map_iff _).mpr ⟨⟨σ q₀, T⟩, hfwd.eval_rev h0 hc', rfl⟩
  · intro hT
    obtain ⟨c, hc, rfl⟩ := (Part.mem_map_iff _).mp hT
    have hq : c.q = σ q₀ := eval_halt_state hM' hc
    have hc' : (⟨σ q₀, c.Tape⟩ : Cfg Γ Λ) ∈
        StateTransition.eval (step M') ⟨σ qf, T'⟩ := by
      rw [← hq]; exact hc
    have h0 : ∀ a, M (σ (σ qf)) a = none := fun a => by
      rw [hσ qf]; exact (hM qf a).mpr rfl
    have := hbwd.eval_rev h0 hc'
    rw [hσ, hσ] at this
    exact (Part.mem_map_iff _).mpr ⟨⟨qf, T'⟩, this, rfl⟩

/-- **Bridge to completeness**: a machine that computes the *same* partial
function as its own reversal computes a partial involution.  Nakano's
completeness construction makes this semantic hypothesis syntactic (via the
`2k`-tape symmetrisation, out of scope for a single-tape model). -/
theorem tapeSem_involutive_of_flip_equiv {M M' : Machine Γ Λ} {σ : Λ → Λ}
    {q₀ qf : Λ} (hσ : ∀ q, σ (σ q) = q)
    (hfwd : FlipOf M M' σ) (hbwd : FlipOf M' M σ)
    (hM : ∀ q a, M q a = none ↔ q = qf)
    (hM' : ∀ q a, M' q a = none ↔ q = σ q₀)
    (hsem : ∀ T, tapeSem M' (σ qf) T = tapeSem M q₀ T)
    {T T' : Tape Γ} (hT' : T' ∈ tapeSem M q₀ T) : T ∈ tapeSem M q₀ T' := by
  have := (tapeSem_inverse hσ hfwd hbwd hM hM').mp hT'
  rwa [hsem] at this

/-- An involutory structure on a `TM0` machine: an involutive state map `σ`
exchanging the start state `q₀` and the halt state `qf`, under which the
rule set is its own flip.  Halting happens exactly at `qf`. -/
structure Involutory (M : Machine Γ Λ) (σ : Λ → Λ) (q₀ qf : Λ) : Prop where
  invol : ∀ q, σ (σ q) = q
  start : σ q₀ = qf
  halt_iff : ∀ q a, M q a = none ↔ q = qf
  flip : FlipOf M M σ

namespace Involutory

variable {M : Machine Γ Λ} {σ : Λ → Λ} {q₀ qf : Λ}

/-- **Config-level soundness**: if an involutory machine, started at `q₀` on
tape `T`, halts at `qf` with tape `T'`, then started on `T'` it halts
with `T`.  Special case `M' = M` of Lecerf reversal. -/
theorem eval_symm (h : Involutory M σ q₀ qf) {T T' : Tape Γ}
    (he : (⟨qf, T'⟩ : Cfg Γ Λ) ∈ StateTransition.eval (step M) ⟨q₀, T⟩) :
    (⟨qf, T⟩ : Cfg Γ Λ) ∈ StateTransition.eval (step M) ⟨q₀, T'⟩ := by
  have hqf : σ qf = q₀ := by
    conv_lhs => rw [← h.start]
    exact h.invol q₀
  have h0 : ∀ a, M (σ q₀) a = none := fun a => by
    rw [h.start]; exact (h.halt_iff qf a).mpr rfl
  have := h.flip.eval_rev h0 he
  rwa [h.start, hqf] at this

theorem halt_state (h : Involutory M σ q₀ qf) {c c' : Cfg Γ Λ}
    (he : c' ∈ StateTransition.eval (step M) c) : c'.q = qf :=
  eval_halt_state h.halt_iff he

/-- **Machine-level soundness** (single-tape core of Nakano Thm 4.2):
the partial tape function computed by an involutory Turing machine is
symmetric, i.e. a partial involution. -/
theorem tapeSem_involutive (h : Involutory M σ q₀ qf) {T T' : Tape Γ}
    (hT' : T' ∈ tapeSem M q₀ T) : T ∈ tapeSem M q₀ T' := by
  obtain ⟨c, hc, rfl⟩ := (Part.mem_map_iff _).mp hT'
  have hq : c.q = qf := h.halt_state hc
  have hc' : (⟨qf, c.Tape⟩ : Cfg Γ Λ) ∈ StateTransition.eval (step M) ⟨q₀, T⟩ := by
    rw [← hq]
    exact hc
  exact (Part.mem_map_iff _).mpr ⟨⟨qf, T⟩, h.eval_symm hc', rfl⟩

end Involutory

section Sanity

/-- Sanity example: the two-state machine that applies `g` to the scanned
symbol and halts. -/
def writeHead (g : Γ → Γ) : Machine Γ Bool := fun q a =>
  match q with
  | true => none
  | false => some (true, Stmt.write (g a))

omit [Inhabited Γ] in
/-- Conversely, if `writeHead g` is involutory then `g` is an involution:
the flip of the rule `(false, a) ↦ (true, write (g a))` demands the rule
`(false, g a) ↦ (true, write a)`, and determinism forces `g (g a) = a`. -/
theorem involution_of_involutory_writeHead {g : Γ → Γ}
    (h : Involutory (writeHead g) not false true) : ∀ a, g (g a) = a := by
  intro a
  have hr := h.flip.flip_write false a true (g a) (by simp [writeHead])
  simpa [writeHead] using hr

omit [Inhabited Γ] in
/-- `writeHead g` is involutory precisely thanks to `g ∘ g = id`. -/
theorem involutory_writeHead (g : Γ → Γ) (hg : ∀ a, g (g a) = a) :
    Involutory (writeHead g) not false true where
  invol := Bool.not_not
  start := rfl
  halt_iff := by intro q a; cases q <;> simp [writeHead]
  flip := by
    constructor
    · intro p a q b hpq
      cases p <;> simp [writeHead] at hpq ⊢
      obtain ⟨rfl, rfl⟩ := hpq
      simp [hg]
    · intro p a q d hpq
      cases p <;> simp [writeHead] at hpq

end Sanity

end PeriodicTM
