/-
FiniteOrderTM/BlockEncode.lean

EXT-2, piece 2a: re-encoding arbitrary finite data as block data over `Option Γ`.

The block-data symmetrisation (`nakano_symmetrisation_strvalued`, BennettStrConj.lean)
needs the input to be a *block* — blank-free on a finite prefix.  Arbitrary finite
data `s : List Γ` may contain internal `Γ`-blanks, so it is not a block over `Γ`.
But over the extended alphabet `Option Γ` (whose blank is the fresh symbol `none`),
the re-encoding `s ↦ Tape.mk₁ (s.map some)` *is* a block: every cell of the prefix is
`some _ ≠ none`, and everything outside is `none`.  This lets the existing block
machinery handle arbitrary finite data, the first step toward relaxing the blank-free
restriction (and ultimately the fully-unconditional goals).

This file proves the foundational fact `encodeStr_isBlock`, plus the `Tape.mk₁`
position lemmas it rests on.
-/
import FiniteOrderTM.BennettStrConj

namespace PeriodicTM

open Turing

variable {Γ : Type*} [Inhabited Γ]

/-- `nth` of `Tape.mk₁` at a nonnegative position is the list's `getI`. -/
theorem mk1_nth_pos (s : List Γ) (k : ℕ) : (Tape.mk₁ s).nth (k : ℤ) = s.getI k := by
  cases k with
  | zero => cases s <;> rfl
  | succ n =>
    show (Tape.mk₁ s).right.nth n = s.getI (n + 1)
    simp only [Tape.mk₁, Tape.mk₂, Tape.mk', ListBlank.tail_mk, ListBlank.nth_mk]
    cases s <;> rfl

/-- `nth` of `Tape.mk₁` at a negative position is the blank. -/
theorem mk1_nth_neg (s : List Γ) (n : ℕ) :
    (Tape.mk₁ s).nth (-(n + 1 : ℕ) : ℤ) = default := by
  show (Tape.mk₁ s).left.nth n = default
  simp only [Tape.mk₁, Tape.mk₂, Tape.mk', ListBlank.nth_mk]; rfl

/-- In-range, `(s.map some).getI` is non-blank (`some _ ≠ none`). -/
theorem map_some_getI_ne (s : List Γ) (i : ℕ) (h : i < s.length) :
    (s.map some).getI i ≠ none := by
  rw [List.getI_eq_getElem _ (by simpa using h), List.getElem_map]
  exact Option.some_ne_none _

/-- Out of range, `(s.map some).getI` is the blank (`none`). -/
theorem map_some_getI_out (s : List Γ) (i : ℕ) (h : s.length ≤ i) :
    (s.map some).getI i = default := by
  unfold List.getI; exact List.getD_eq_default _ _ (by simpa using h)

/-- Re-encode finite `Γ`-data as a tape over `Option Γ` (blank `= none`). -/
def encodeStr (s : List Γ) : Tape (Option Γ) := Tape.mk₁ (s.map some)

/-- **EXT-2 piece 2a: the re-encoding is a block.**  `encodeStr s` is blank-free on
the prefix `[0, s.length)` (each cell is `some _`) and blank (`none`) outside, so it
is `IsBlock` over `Option Γ` — for *arbitrary* finite data, even with internal
`Γ`-blanks. -/
theorem encodeStr_isBlock (s : List Γ) : IsBlock (encodeStr s) := by
  refine ⟨s.length, ?_, ?_⟩
  · intro i hi
    rw [encodeStr, mk1_nth_pos]
    exact map_some_getI_ne s i hi
  · intro m hm
    rcases lt_or_ge m 0 with hneg | hpos
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = -((k : ℤ) + 1) := ⟨(-m - 1).toNat, by omega⟩
      have he : -((k : ℤ) + 1) = -(((k + 1 : ℕ)) : ℤ) := by omega
      rw [encodeStr, he]
      exact mk1_nth_neg (s.map some) k
    · have hj : (↑m.toNat : ℤ) = m := Int.toNat_of_nonneg hpos
      rw [encodeStr, ← hj, mk1_nth_pos]
      apply map_some_getI_out
      omega

/-- Decoding `Option Γ → Γ` is a `PointedMap` (the fresh blank `none` maps to `Γ`'s
blank), so it acts on whole tapes via `Tape.map`. -/
def decodePointed : PointedMap (Option Γ) Γ := ⟨(·.getD default), rfl⟩

/-- **The re-encoding is faithfully decodable.**  Mapping `encodeStr s` through the
decode pointed-map recovers the standard tape `Tape.mk₁ s`.  So no information is
lost: the `Option Γ` block carries exactly the original data. -/
theorem decode_encode (s : List Γ) :
    Tape.map (decodePointed (Γ := Γ)) (encodeStr s) = Tape.mk₁ s := by
  rw [encodeStr, Tape.map_mk₁, List.map_map]
  congr 1
  exact List.map_id s

/-- **EXT-2 payoff: arbitrary finite data is symmetrisable after re-encoding.**
For *any* finite data `s : List Γ` (even with internal `Γ`-blanks) and any
blank-fixing cellwise involution `g` over the extended alphabet `Option Γ`, the
re-encoded input `encodeStr s` is a legitimate input to the existing block
symmetrisation `bennettBStrD (cellwiseM0 g)`: the conjugated machine carries
`encodeStr s` to (the encoding of) its involution image `U` and back.

This is the concrete reason `encodeStr_isBlock` matters — it lifts the
blank-free block restriction of `nakano_symmetrisation_strvalued` to *arbitrary*
finite `Γ`-data, with no hypothesis on `g` beyond being a blank-fixing
involution.  (It does not close the fully-unconditional `sorry`s, which would
need a hypothesis bounding an *arbitrary* `M₀` to the data region.) -/
theorem encodeStr_cellwise_symmetrisable [DecidableEq Γ]
    (g : Option Γ → Option Γ) (hg : ∀ x, g (g x) = x) (hgdef : g default = default)
    (s : List Γ) :
    ∃ (q0' : _)
      (enc : (Unit → Tape (Option Γ)) →
        ((Unit ⊕ Fin 1) ⊕ Unit → Tape (BennettAlph2 (Option Γ) Bool Unit)))
      (U : Unit → Tape (Option Γ)),
      U ∈ ktapeSem (cellwiseM0 g) false (fun _ => encodeStr s) ∧
      enc U ∈ ktapeSem (bennettBStrD (cellwiseM0 g) false) q0'
        (enc (fun _ => encodeStr s)) ∧
      enc (fun _ => encodeStr s) ∈ ktapeSem (bennettBStrD (cellwiseM0 g) false) q0'
        (enc U) := by
  obtain ⟨q0', enc, h⟩ := cellwiseM0_strvalued (Γ := Option Γ) g hg hgdef
  refine ⟨q0', enc,
    (KStmt.write (fun i => g (headsV (fun _ : Unit => encodeStr s) i))).apply
      (fun _ : Unit => encodeStr s), ?_, ?_⟩
  · exact (cellwiseM0_sem g (fun _ => encodeStr s) _).mpr rfl
  · exact h (fun _ => encodeStr s) _ (fun _ => encodeStr_isBlock s)
      ((cellwiseM0_sem g (fun _ => encodeStr s) _).mpr rfl)

end PeriodicTM
