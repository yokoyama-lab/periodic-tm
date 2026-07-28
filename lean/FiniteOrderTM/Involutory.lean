/-
FiniteOrderTM/Involutory.lean

Syntactic involutority for the single-tape `TM0` model and the first step of
the mechanisation of Nakano's ITM completeness theorem (RC 2020: every
computable involution is computed by an involutory Turing machine).

* `SyntacticallyInvolutory M q₀ qf` — there exists a state involution `σ`
  exchanging `q₀`/`qf` under which `M`'s rule set is exactly its own
  Lecerf flip (packaged via the existing `Involutory` predicate from
  `Machine.lean`; with `σ` involutive, `FlipOf M M σ` closes the rule set
  under flipping in both directions, so "renaming the reversal by `σ`
  gives back `M`" holds exactly, mirroring Nakano's syntactic condition
  and the Python prototype `invcomp/itm_backend.py`
  (`is_syntactically_involutory`)).

* `renameM` and `Involutory.renameM_self` — involutority is preserved by
  the `σ`-renaming itself (the renamed machine is involutory with start
  and halt states exchanged).

* `syntacticallyInvolutory_writeHead_iff` — the one-cell writer
  `writeHead g` (rules `(q0, s) ↦ (write (g s), halt)`, `σ = not`
  swapping `q0`/`halt`, exactly the machine `build_write_machine`
  produces in `itm_backend.py`) is syntactically involutory *iff* `g` is
  an involution; `tapeSem_writeHead` computes its semantics and
  `tapeSem_writeHead_twice` shows the induced tape function is an
  involution.

* `CompletenessGoal` — statement (as a `Prop`, no admitted proof) of the full
  completeness target at tape-semantics level, and
  `completenessGoal_oneCell` — the proved one-cell instance: every
  involution on the alphabet is computed by a syntactically involutory
  machine (Lean twin of the `itm_backend.py` checks (a)+(b)).
-/
import FiniteOrderTM.Machine

namespace PeriodicTM

open Turing Turing.TM0

variable {Γ : Type*} [Inhabited Γ]
variable {Λ : Type*} [Inhabited Λ]

/-! ### Syntactic involutority -/

/-- **Syntactic involutority**: some involutive state renaming `σ` with
`σ q₀ = qf` turns `M`'s rule set into exactly its own Lecerf reversal, and
`M` halts exactly at `qf`.  This is the machine-level syntactic symmetry
condition of Nakano's involutory Turing machines: `FlipOf M M σ` says every
rule's `σ`-flip is again a rule, and since flipping (with `σ` involutive) is
an involution on rules, the flip of the rule set coincides with the rule
set — i.e. renaming `M`'s reversal by `σ` yields exactly `M`. -/
def SyntacticallyInvolutory (M : Machine Γ Λ) (q₀ qf : Λ) : Prop :=
  ∃ σ : Λ → Λ, Involutory M σ q₀ qf

/-- A syntactically involutory machine computes a partial involution on
tapes (semantic soundness, inherited from `Involutory.tapeSem_involutive`). -/
theorem SyntacticallyInvolutory.tapeSem_symm {M : Machine Γ Λ} {q₀ qf : Λ}
    (h : SyntacticallyInvolutory M q₀ qf) {T T' : Tape Γ}
    (hT' : T' ∈ tapeSem M q₀ T) : T ∈ tapeSem M q₀ T' := by
  obtain ⟨σ, hσ⟩ := h
  exact hσ.tapeSem_involutive hT'

/-! ### Renaming by the state involution -/

/-- Rename the states of a machine along `σ` (conjugation when `σ` is an
involution): rule `(p, a) ↦ (q, s)` becomes `(σ p, a) ↦ (σ q, s)`. -/
def renameM (σ : Λ → Λ) (M : Machine Γ Λ) : Machine Γ Λ := fun q a =>
  (M (σ q) a).map fun r => (σ r.1, r.2)

omit [Inhabited Γ] in
/-- **Involutority is preserved by the `σ`-renaming itself**: conjugating an
involutory machine by its own state involution yields an involutory machine
(with start and halt states exchanged, since `σ q₀ = qf`). -/
theorem Involutory.renameM_self {M : Machine Γ Λ} {σ : Λ → Λ} {q₀ qf : Λ}
    (h : Involutory M σ q₀ qf) : Involutory (renameM σ M) σ qf q₀ := by
  have hqf : σ qf = q₀ := by
    conv_lhs => rw [← h.start]
    exact h.invol q₀
  refine ⟨h.invol, hqf, ?_, ?_, ?_⟩
  · intro q a
    constructor
    · intro hn
      have : M (σ q) a = none := by
        rcases e : M (σ q) a with - | r
        · rfl
        · simp [renameM, e] at hn
      have : σ q = qf := (h.halt_iff (σ q) a).mp this
      calc q = σ (σ q) := (h.invol q).symm
        _ = σ qf := by rw [this]
        _ = q₀ := hqf
    · intro hq
      have : M (σ q) a = none := by
        rw [hq, h.start]; exact (h.halt_iff qf a).mpr rfl
      simp [renameM, this]
  · intro p a q b hpq
    rcases e : M (σ p) a with - | ⟨q', s⟩
    · simp [renameM, e] at hpq
    · have hqs : σ q' = q ∧ s = Stmt.write b := by
        have := hpq
        simp [renameM, e] at this
        exact ⟨this.1, this.2⟩
      obtain ⟨hq, rfl⟩ := hqs
      have hr := h.flip.flip_write (σ p) a q' b e
      -- `hr : M (σ q') b = some (σ (σ p), write a)`; rewrite states
      rw [h.invol p] at hr
      have hσq : σ (σ q) = σ q' := by rw [← hq, h.invol]
      show (M (σ (σ q)) b).map _ = _
      rw [hσq, hr]
      rfl
  · intro p a q d hpq b
    rcases e : M (σ p) a with - | ⟨q', s⟩
    · simp [renameM, e] at hpq
    · have hqs : σ q' = q ∧ s = Stmt.move d := by
        have := hpq
        simp [renameM, e] at this
        exact ⟨this.1, this.2⟩
      obtain ⟨hq, rfl⟩ := hqs
      have hr := h.flip.flip_move (σ p) a q' d e b
      rw [h.invol p] at hr
      have hσq : σ (σ q) = σ q' := by rw [← hq, h.invol]
      show (M (σ (σ q)) b).map _ = _
      rw [hσq, hr]
      rfl

omit [Inhabited Γ] in
/-- Syntactic involutority is preserved by conjugation with the witnessing
state involution (start/halt exchanged). -/
theorem SyntacticallyInvolutory.renameM {M : Machine Γ Λ} {σ : Λ → Λ}
    {q₀ qf : Λ} (h : Involutory M σ q₀ qf) :
    SyntacticallyInvolutory (renameM σ M) qf q₀ :=
  ⟨σ, h.renameM_self⟩

/-! ### The one-cell writer (Lean twin of `itm_backend.build_write_machine`) -/

omit [Inhabited Γ] in
/-- **The one-cell writer is syntactically involutory iff it writes an
involution.**  `writeHead g` is exactly the machine of the Python prototype
(`itm_backend.py`): rules `(q0, s) ↦ (write (g s), halt)` with the state
involution `σ = not` swapping `q0 = false` and `halt = true`.  Forward
direction: since an involutive `σ : Bool → Bool` with `σ false = true` must
be `not`, the flip condition forces `g (g a) = a` by determinism.  Backward:
`involutory_writeHead`. -/
theorem syntacticallyInvolutory_writeHead_iff (g : Γ → Γ) :
    SyntacticallyInvolutory (writeHead g) false true ↔ ∀ a, g (g a) = a := by
  constructor
  · rintro ⟨σ, h⟩
    have hσ : σ = not := by
      funext b
      cases b
      · exact h.start
      · calc σ true = σ (σ false) := by rw [h.start]
          _ = false := h.invol false
    rw [hσ] at h
    exact involution_of_involutory_writeHead h
  · intro hg
    exact ⟨not, involutory_writeHead g hg⟩

/-- Semantics of the one-cell writer: on tape `T` it halts with the scanned
symbol rewritten to `g T.1`. -/
theorem tapeSem_writeHead (g : Γ → Γ) (T : Tape Γ) :
    tapeSem (writeHead g) false T = Part.some (T.write (g T.1)) := by
  apply Part.eq_some_iff.mpr
  apply (Part.mem_map_iff _).mpr
  refine ⟨⟨true, T.write (g T.1)⟩, ?_, rfl⟩
  refine StateTransition.mem_eval.mpr ⟨?_, ?_⟩
  · exact Relation.ReflTransGen.single (by simp [step, writeHead])
  · simp [step, writeHead]

/-- If `g` is an involution then the tape function computed by `writeHead g`
is an involution: running the machine twice is the identity on tapes. -/
theorem tapeSem_writeHead_twice (g : Γ → Γ) (hg : ∀ a, g (g a) = a)
    (T : Tape Γ) :
    (tapeSem (writeHead g) false T).bind (tapeSem (writeHead g) false) =
      Part.some T := by
  rw [tapeSem_writeHead, Part.bind_some, tapeSem_writeHead]
  have hhead : (T.write (g T.1)).1 = g T.1 := rfl
  rw [hhead, tape_write_write, hg, Tape.write_self]

/-! ### The completeness target -/

/-- **Statement of Nakano's completeness theorem** (RC 2020, Thm 4.6) at
tape-semantics level for the `TM0` model, as a `Prop` (the proof is the main
open formalisation target — see the roadmap below):

Every partial tape involution *computed by some machine* — this is exactly
"computable" internal to the model — is computed by a syntactically
involutory machine, on a possibly enlarged state space.

The strict semantic equality `tapeSem M' q₀' T = tapeSem M q₀ T` is the
one-tape idealisation; Nakano's actual construction works up to the string
I/O convention and Bennett-style history bookkeeping, so the eventual
mechanised theorem may replace equality by agreement on encoded inputs
(see `IOConvention.lean`). -/
def CompletenessGoal : Prop :=
  ∀ (Γ Λ : Type) (_ : Inhabited Γ) (iΛ : Inhabited Λ)
    (M : @Machine Γ Λ iΛ) (q₀ qf : Λ),
    (∀ q a, M q a = none ↔ q = qf) →
    (∀ T T', T' ∈ tapeSem M q₀ T → T ∈ tapeSem M q₀ T') →
    ∃ (Λ' : Type) (iΛ' : Inhabited Λ') (M' : @Machine Γ Λ' iΛ')
      (q₀' qf' : Λ'),
      @SyntacticallyInvolutory Γ Λ' iΛ' M' q₀' qf' ∧
      ∀ T, tapeSem M' q₀' T = tapeSem M q₀ T

/-- **One-cell completeness** (proved): every involution `g` on the alphabet
is computed — as the one-cell tape transformation `T ↦ T.write (g T.1)` — by
a syntactically involutory machine, namely `writeHead g`.  This is the Lean
twin of the `itm_backend.py` result (checks (a) syntactic involutority and
(b) machine-level `f ∘ f = id` for the compiled one-cell machines). -/
theorem completenessGoal_oneCell (g : Γ → Γ) (hg : ∀ a, g (g a) = a) :
    ∃ (M : Machine Γ Bool) (q₀ qf : Bool),
      SyntacticallyInvolutory M q₀ qf ∧
      ∀ T : Tape Γ, tapeSem M q₀ T = Part.some (T.write (g T.1)) :=
  ⟨writeHead g, false, true,
    (syntacticallyInvolutory_writeHead_iff g).mpr hg, tapeSem_writeHead g⟩

/-!
### Roadmap to full `CompletenessGoal`

The one-cell case (`completenessGoal_oneCell`) is the finite kernel.  The
path to the general theorem, following Nakano (RC 2020) and the pieces
already in this repository:

1. **String I/O encoding** (`IOConvention.lean` / `IOConventionInstance.lean`):
   replace the one-cell transformation by input/output words under the
   standard-configuration convention, so that "computable involution" means
   an involution on `List Γ` computed by some machine w.r.t. the encoding.
   `CompletenessGoal` should then be restated up to encoding rather than
   strict `tapeSem` equality.

2. **Lecerf reversal, syntactically** (`Flip.lean`, plus `FlipOf` here):
   from a reversible `M` construct the reversed machine `M⁻` with
   `FlipOf M M⁻ σ` and `FlipOf M⁻ M σ` *definitionally* (backward
   determinism of `M` makes `M⁻` a well-defined deterministic machine);
   `tapeSem_inverse` then gives `⟦M⁻⟧ = ⟦M⟧⁻¹` for free.

3. **Bennett history + symmetrisation** (`Symmetrise.lean`,
   `MultiTape.lean`): a general computable involution `f` need not be
   computed by any machine that is *syntactically* symmetric; Nakano's
   construction runs `M` forward recording a Bennett history, applies the
   involution, and retracts the history with `M⁻`, arranging the state
   space and tape banks (`2k` tapes, tape-bank permutation as the state
   involution `σ`) so that the combined rule table is exactly its own flip.
   The multi-tape machinery must then be transported back to the one-tape
   model (`Lift.lean` / `Reindex.lean`) or `CompletenessGoal` restated for
   the multi-tape model.

4. **Assembly**: combine 1–3 to discharge `CompletenessGoal` (in its
   encoding-aware form), with `completenessGoal_oneCell` as the base
   sanity instance and `Involutory.tapeSem_involutive` as the converse
   (soundness) direction already in `Machine.lean`.
-/

end PeriodicTM
