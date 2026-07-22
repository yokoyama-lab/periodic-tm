/-
FiniteOrderTM/IOConventionInstance.lean

#4 follow-up (self-review action #2): a concrete, non-vacuous `StdOutput` instance.

`stringSem_involutive` (IOConvention.lean) shows an involutory machine with
`StdOutput` computes a partial involution on strings, but leaves `StdOutput`
unwitnessed.  Here we discharge it for the head-write machine `writeHead g`
(write `g` at the head, halt) when `g` is a blank-fixing involution:

* `singleWrite_tapeSem` — the TM0 analogue of `singleWrite_ktapeSem`: a
  one-write-then-halt machine's tape semantics is the single head write.
* `writeHead_stdOutput` — `writeHead g` has standard output (`g default =
  default` makes the empty-input tape stay blank, via `ListBlank`'s trailing-
  blank quotient).
* `stringSem_writeHead_involutive` — combining with `involutory_writeHead`,
  `writeHead g` computes a partial involution *on strings*: the string-level
  theorem is non-vacuous on a genuinely computing machine.
-/
import FiniteOrderTM.IOConvention
import FiniteOrderTM.Machine

namespace PeriodicTM

open Turing Turing.TM0

variable {Γ : Type*} [Inhabited Γ] {Λ : Type*} [Inhabited Λ]

/-- **Semantics of a one-write-then-halt TM0 machine** (single-tape analogue of
`singleWrite_ktapeSem`): writing `w` at the head from `false` and halting at
`true` gives the single head write. -/
theorem singleWrite_tapeSem (M : Machine Γ Bool) (w : Γ → Γ)
    (hstep : ∀ a, M false a = some (true, Stmt.write (w a)))
    (hhalt : ∀ a, M true a = none) (T V : Tape Γ) :
    V ∈ tapeSem M false T ↔ V = T.write (w T.1) := by
  have hstep1 : step M ⟨false, T⟩ = some ⟨true, T.write (w T.1)⟩ := by
    simp only [step, hstep, Option.map_some]
  have hhalt2 : ∀ X, step M (⟨true, X⟩ : Cfg Γ Bool) = none := by
    intro X; simp only [step, hhalt]; rfl
  constructor
  · intro hV
    obtain ⟨c, hc, rfl⟩ := (Part.mem_map_iff _).mp hV
    obtain ⟨hr, hcfhalt⟩ := StateTransition.mem_eval.mp hc
    rcases Relation.ReflTransGen.cases_head hr with heq | ⟨b, hb, hrest⟩
    · rw [← heq, hstep1] at hcfhalt; exact absurd hcfhalt (by simp)
    · have hbeq : b = (⟨true, T.write (w T.1)⟩ : Cfg Γ Bool) := by
        rw [Option.mem_def, hstep1] at hb; exact (Option.some.inj hb).symm
      subst hbeq
      rcases Relation.ReflTransGen.cases_head hrest with heq2 | ⟨b2, hb2, _⟩
      · exact (congrArg Cfg.Tape heq2).symm
      · rw [Option.mem_def, hhalt2] at hb2; exact absurd hb2 (by simp)
  · intro hV; subst hV
    refine (Part.mem_map_iff _).mpr
      ⟨⟨true, T.write (w T.1)⟩,
        StateTransition.mem_eval.mpr ⟨?_, hhalt2 _⟩, rfl⟩
    exact Relation.ReflTransGen.single (Option.mem_def.mpr hstep1)

/-- Writing `c` at the head of a standard tape gives a standard tape:
`(mk₁ s).write c = mk₁ (c :: s.tail)` (uniform in `s`, including `s = []`). -/
theorem mk1_write (c : Γ) (s : List Γ) :
    (Tape.mk₁ s).write c = Tape.mk₁ (c :: s.tail) := by
  simp only [Tape.write, Tape.mk₁, Tape.mk₂, Tape.mk', List.tail_cons,
    ListBlank.tail_mk, ListBlank.head_mk]
  cases s <;> rfl

/-- **`writeHead g` has standard output** when `g` fixes the blank.  On `mk₁ s`
the output is `(mk₁ s).write (g s.headI) = mk₁ (g s.headI :: s.tail)`, a standard
tape; the empty case needs `g default = default` so the all-blank tape is
preserved (`ListBlank` quotients trailing blanks). -/
theorem writeHead_stdOutput (g : Γ → Γ) (hgdef : g default = default) :
    StdOutput (writeHead g) false := by
  constructor
  intro s T' hT'
  rw [singleWrite_tapeSem (writeHead g) g (fun _ => rfl) (fun _ => rfl)] at hT'
  subst hT'
  cases s with
  | nil =>
    have hc : g (Tape.mk₁ ([] : List Γ)).1 = (Tape.mk₁ ([] : List Γ)).1 := hgdef
    rw [hc, Tape.write_self]
    rfl
  | cons a t =>
    rw [mk1_write]
    simp only [List.tail_cons, List.length_cons]
    rw [show t.length + 1
          = (g (Tape.mk₁ (a :: t)).head :: t).length from rfl, readTape_mk₁]

/-- **The string-level theorem is non-vacuous.**  For a blank-fixing involution
`g`, `writeHead g` computes a partial involution on strings: it is involutory
(`involutory_writeHead`) and has standard output (`writeHead_stdOutput`), so
`stringSem_involutive` applies.  A concrete \textsf{StdOutput} witness on a
genuinely computing machine. -/
theorem stringSem_writeHead_involutive (g : Γ → Γ)
    (hg : ∀ a, g (g a) = a) (hgdef : g default = default) :
    ∀ s s', s' ∈ stringSem (writeHead g) false s →
            s ∈ stringSem (writeHead g) false s' :=
  stringSem_involutive (involutory_writeHead g hg) (writeHead_stdOutput g hgdef)

end PeriodicTM
