/-
FiniteOrderTM/IOConvention.lean

M6c: Input/output convention for single-tape TM0.

Bridges the whole-tape semantics `tapeSem` to a string-level partial
function.  The convention follows Axelsen and Glück: a string `s` is
placed on an otherwise-blank tape with the head at the first symbol
(`Tape.mk₁ s`); output is read as the same number of symbols from the
head of the halted tape.

The key theorems:

* `readTape_left_irrelevant`: readTape only reads head and right, so the
  left side of the tape is irrelevant.  (Tape geometry; proved by induction
  on n.)

* `readTape_mk₁`: reading `s.length` symbols from `Tape.mk₁ s` gives back
  `s`.  (Tape geometry; proved from left-irrelevance.)

* `stringSem_involutive`: the bridge theorem — an involutory machine with
  `StdOutput` computes a partial involution on strings.  This is the only
  theorem that requires `tapeSem_involutive` from Machine.lean.

The `StdOutput` condition (the machine returns the head to position 0 and
produces a left-blank tape) is a property of Nakano's symmetrisation
construction; verifying it for the 2k-tape completeness construction is
the main remaining proof obligation.
-/
import FiniteOrderTM.Machine

namespace PeriodicTM

open Turing Turing.TM0

variable {Γ : Type*} [Inhabited Γ] {Λ : Type*} [Inhabited Λ]

/-! ### Standard tape representation -/

/-- Read `n` symbols from the tape, starting at the head and moving right.
This is the output-reading function: `readTape n T` returns the `n` symbols
at positions 0, 1, …, n−1 of the tape `T`. -/
def readTape : ℕ → Tape Γ → List Γ
  | 0,     _ => []
  | n + 1, T => T.head :: readTape n (T.move Dir.right)

@[simp] theorem readTape_length (n : ℕ) (T : Tape Γ) :
    (readTape n T).length = n := by
  induction n generalizing T with
  | zero => rfl
  | succ n ih => simp [readTape, ih]

/-- `readTape` only accesses head and right; the left side is irrelevant.
Proof by induction: moving right propagates head and right while only
modifying left, so left never enters the computation. -/
theorem readTape_left_irrelevant (n : ℕ) {T₁ T₂ : Tape Γ}
    (hh : T₁.head = T₂.head) (hr : T₁.right = T₂.right) :
    readTape n T₁ = readTape n T₂ := by
  induction n generalizing T₁ T₂ with
  | zero => rfl
  | succ n ih =>
    simp only [readTape, hh]
    apply congrArg
    apply ih
    · simp [Tape.move, hr]
    · simp [Tape.move, hr]

/-- Reading `s.length` symbols from the standard tape `Tape.mk₁ s` gives
back `s`.  The proof unfolds the list cons-by-cons; at each step we use
`readTape_left_irrelevant` to discard the left-accumulation that `move
Dir.right` adds, leaving a tape identical to `Tape.mk₁ t` in the relevant
(head, right) fields. -/
theorem readTape_mk₁ (s : List Γ) : readTape s.length (Tape.mk₁ s) = s := by
  induction s with
  | nil => rfl
  | cons a t ih =>
    simp only [readTape, Tape.mk₁, Tape.mk₂, Tape.mk']
    rw [show ListBlank.mk (a :: t) = ListBlank.cons a (ListBlank.mk t) from
          (ListBlank.cons_mk a t).symm]
    simp only [ListBlank.head_cons, ListBlank.tail_cons]
    -- Goal: a :: readTape t.length (move right { head=a, left=mk[], right=mk t }) = a :: t
    congr 1
    simp only [Tape.move]
    -- Goal: readTape t.length { head=(mk t).head, left=cons a (mk[]), right=(mk t).tail } = t
    -- Use calc to avoid rw [← ih] polluting the LHS
    calc readTape t.length { head := (ListBlank.mk t).head,
                              left := ListBlank.cons a (ListBlank.mk []),
                              right := (ListBlank.mk t).tail }
        = readTape t.length (Tape.mk₁ t) := by
            apply readTape_left_irrelevant
            · simp [Tape.mk₁, Tape.mk₂, Tape.mk']
            · simp [Tape.mk₁, Tape.mk₂, Tape.mk']
      _ = t := ih

/-! ### String-level semantics -/

/-- A machine `M` has **standard output** at `q₀` if, whenever it starts on a
standard tape `Tape.mk₁ s`, the output tape is itself standard: its left
side is blank and head is at the first output symbol.  Concretely: the
output tape equals `Tape.mk₁ (readTape s.length T')`.

This is a property of the symmetrisation construction (Nakano's 2k-tape
completeness), not of the soundness theory.  All soundness results hold
without it; it is needed only to close the I/O loop. -/
structure StdOutput (M : Machine Γ Λ) (q₀ : Λ) : Prop where
  left_blank : ∀ s (T' : Tape Γ),
      T' ∈ tapeSem M q₀ (Tape.mk₁ s) →
      T' = Tape.mk₁ (readTape s.length T')

/-- The string-level partial function: run `M` on `Tape.mk₁ s` and read
`s.length` symbols from the output tape. -/
noncomputable def stringSem (M : Machine Γ Λ) (q₀ : Λ) (s : List Γ) :
    Part (List Γ) :=
  (tapeSem M q₀ (Tape.mk₁ s)).map (readTape s.length)

/-- An involutory machine with standard output computes a partial involution
on strings.

**Proof sketch**: given `s' ∈ stringSem M q₀ s`, there exists
`T' ∈ tapeSem M q₀ (mk₁ s)` with `s' = readTape |s| T'`.

1. *StdOutput*: `T' = mk₁ s'`.
2. *tapeSem_involutive* (from Machine.lean): `mk₁ s ∈ tapeSem M q₀ T' =
   tapeSem M q₀ (mk₁ s')`.
3. *readTape_mk₁*: `readTape |s'| (mk₁ s) = s` (since `|s'| = |s|` by
   `readTape_length`).

Hence `s ∈ stringSem M q₀ s'`. -/
theorem stringSem_involutive
    {M : Machine Γ Λ} {σ : Λ → Λ} {q₀ qf : Λ}
    (hM  : Involutory M σ q₀ qf)
    (hSO : StdOutput M q₀) :
    ∀ s s', s' ∈ stringSem M q₀ s → s ∈ stringSem M q₀ s' := by
  intro s s' hs
  simp only [stringSem, Part.mem_map_iff] at hs ⊢
  obtain ⟨T', hT', hrT'⟩ := hs
  -- Step 1: StdOutput gives T' = mk₁ s'
  have hT'_std : T' = Tape.mk₁ s' := by
    rw [← hrT']; exact hSO.left_blank s T' hT'
  -- Step 2: involutory soundness: mk₁ s ∈ tapeSem M q₀ T'
  have hrev : Tape.mk₁ s ∈ tapeSem M q₀ T' :=
    hM.tapeSem_involutive hT'
  rw [hT'_std] at hrev
  -- Step 3: s' and s have the same length
  have hlen : s'.length = s.length := by
    have := readTape_length s.length T'
    rw [hrT'] at this
    omega
  -- Conclude
  refine ⟨Tape.mk₁ s, hrev, ?_⟩
  rw [hlen, readTape_mk₁]

end PeriodicTM
