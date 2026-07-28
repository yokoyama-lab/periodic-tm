/-
FiniteOrderTM/InvComp.lean

The involution compiler, mechanized (mirrors `invcomp/invcomp.py`).

A mini reversible language over an abstract state type `α` is deep-embedded as
`Prog α` (Prim / Seq / Call k / Reflect mode), following the Python AST:
`prim` carries an explicit fwd/bwd pair with inverse proofs, `seq` runs left to
right, `call` is a `k`-th power with `k : ℤ` (negative = backward), and
`reflect` is the orbit-walk reflection combinator — the core of the compiler
output.

Denotation `den : Prog α → Equiv.Perm α` returns a *permutation*, so
`run`/`run_bwd` of the prototype are the two directions of one `Equiv`
(`⇑(den P)` and `⇑(den P).symm`), and `den_bijective` is free.

Design decision (threading of `LocallyFinite`): the denotation of
`reflect P m` must be `LF.iota1 / LF.iota2` of `⇑(den P)`, which require a
`LocallyFinite` proof.  We make `den` *total* by a classical case split
(`reflPerm`): if `LocallyFinite ⇑(den P)` holds, the reflection is the
corresponding iota (packaged as a `Perm` via its involution proof); otherwise
it is `1`.  A syntactic well-formedness predicate `WF` — the Lean counterpart
of `check_locally_finite` — certifies that every `reflect` node in a program
sits on a locally finite subdenotation, so on well-formed programs the
classical split always takes the true branch.  This keeps `den`
non-dependent (no proof argument), and the correctness theorems take the
`LocallyFinite` hypothesis exactly where the semantics needs it.
This is variant (a)+(b) of the design space: total `den` via classical choice,
plus an inductive `WF` for the syntactic certificate.

Correctness (the point of the file): for `compile P = (I1, I2)`,
`den I1 ∘ den I2 = den P` whenever `⇑(den P)` is locally finite
(`compile_correct`), and both outputs are involutions *unconditionally*
(`compile_involutive₁/₂`) — direct corollaries of
`locallyFinite_eq_two_involutions` in `LocallyFinite.lean`.

Roadmap: the `reflect` denotation is machine-model-agnostic.  Future backends:
* SRL backend — realize `reflect` as a transposition cascade (each orbit
  reversed by adjacent swaps), compiling `Prog` to loop-free SRL programs;
* ITM backend (Nakano RC 2020) — compile each involution `I1, I2` to an
  involutory Turing machine, connecting to `FiniteOrderTM/Involutory.lean`
  and `Machine.lean`.
-/
import Mathlib
import FiniteOrderTM.Basic
import FiniteOrderTM.LocallyFinite

namespace PeriodicTM
namespace InvComp

open Function

variable {α : Type*}

attribute [local instance] Classical.propDecidable

/-- Reflection mode: `i1` is `k ↦ 1 - k`, `i2` is `k ↦ -k` (mod orbit length),
mirroring `Reflect(prog, mode)` with `mode ∈ {"i1", "i2"}`. -/
inductive RMode : Type
  | i1 : RMode
  | i2 : RMode
  deriving DecidableEq, Repr

/-- The mini reversible language (mirrors the Python AST).  `prim` carries a
forward/backward pair with both inverse laws, as `Prim(name, fwd, bwd)` does
semantically; `seq` is binary (the Python tuple folds into it); `call` is the
`k`-th power, `k : ℤ`; `reflect` is the orbit-reflection combinator. -/
inductive Prog (α : Type*) where
  | prim (fwd bwd : α → α)
      (bf : ∀ x, bwd (fwd x) = x) (fb : ∀ x, fwd (bwd x) = x) : Prog α
  | seq (p q : Prog α) : Prog α
  | call (p : Prog α) (k : ℤ) : Prog α
  | reflect (p : Prog α) (m : RMode) : Prog α

/-- Package an involution as a permutation (its own inverse). -/
def involPerm (f : α → α) (h : IsInvolution f) : Equiv.Perm α :=
  ⟨f, f, h, h⟩

@[simp] theorem coe_involPerm (f : α → α) (h : IsInvolution f) :
    ⇑(involPerm f h) = f := rfl

/-- Denotation of the reflection combinator applied to an already-denoted
permutation `f`: the orbit reflection `LF.iota1` / `LF.iota2` when `⇑f` is
locally finite, and `1` otherwise (the classical escape hatch that keeps
`den` total; `WF` rules this branch out). -/
noncomputable def reflPerm (f : Equiv.Perm α) (m : RMode) : Equiv.Perm α :=
  if h : LocallyFinite ⇑f then
    match m with
    | .i1 => involPerm (LF.iota1 ⇑f h) (LF.iota1_involution h)
    | .i2 => involPerm (LF.iota2 ⇑f h) (LF.iota2_involution h)
  else 1

/-- Denotation, mirroring `run` (and, through `Equiv.symm`, `run_bwd`):
programs denote permutations of the state space. -/
noncomputable def den : Prog α → Equiv.Perm α
  | .prim f g bf fb => ⟨f, g, bf, fb⟩
  | .seq p q => (den p).trans (den q)
  | .call p k => den p ^ k
  | .reflect p m => reflPerm (den p) m

@[simp] theorem den_prim (f g : α → α) (bf fb) :
    ⇑(den (Prog.prim f g bf fb)) = f := rfl

@[simp] theorem den_seq (p q : Prog α) (x : α) :
    den (p.seq q) x = den q (den p x) := rfl

@[simp] theorem den_call (p : Prog α) (k : ℤ) :
    den (p.call k) = den p ^ k := rfl

/-- `run_bwd` on a backward call agrees with a forward call of the negated
power (`run_bwd(Call(p, k)) = run(Call(p, -k))` in the prototype). -/
theorem den_call_symm (p : Prog α) (k : ℤ) :
    (den (p.call k)).symm = den (p.call (-k)) := by
  simp [den, zpow_neg, Equiv.Perm.inv_def]

/-- Every program denotes a bijection (mirrors reversibility of `run`). -/
theorem den_bijective (p : Prog α) : Function.Bijective ⇑(den p) :=
  (den p).bijective

theorem den_reflect_i1 (p : Prog α) (h : LocallyFinite ⇑(den p)) :
    ⇑(den (p.reflect .i1)) = LF.iota1 ⇑(den p) h := by
  show ⇑(reflPerm (den p) .i1) = _
  rw [reflPerm, dif_pos h]
  rfl

theorem den_reflect_i2 (p : Prog α) (h : LocallyFinite ⇑(den p)) :
    ⇑(den (p.reflect .i2)) = LF.iota2 ⇑(den p) h := by
  show ⇑(reflPerm (den p) .i2) = _
  rw [reflPerm, dif_pos h]
  rfl

/-- A reflection node is an involution *unconditionally*: on the locally
finite branch it is an iota, on the escape branch it is `1`. -/
theorem den_reflect_involutive (p : Prog α) (m : RMode) :
    IsInvolution ⇑(den (p.reflect m)) := by
  show IsInvolution ⇑(reflPerm (den p) m)
  by_cases h : LocallyFinite ⇑(den p)
  · cases m
    · rw [reflPerm, dif_pos h]; exact LF.iota1_involution h
    · rw [reflPerm, dif_pos h]; exact LF.iota2_involution h
  · rw [reflPerm, dif_neg h]; intro x; rfl

/-! ### Well-formedness (the Lean `check_locally_finite`) -/

/-- Syntactic certificate that every `reflect` node sits on a locally finite
subdenotation — the mechanized counterpart of `check_locally_finite`.  On
well-formed programs the classical split inside `reflPerm` always takes the
true branch, so `den` computes the intended orbit reflections throughout. -/
inductive WF : Prog α → Prop where
  | prim (f g : α → α) (bf fb) : WF (Prog.prim f g bf fb)
  | seq {p q : Prog α} : WF p → WF q → WF (p.seq q)
  | call {p : Prog α} (k : ℤ) : WF p → WF (p.call k)
  | reflect {p : Prog α} (m : RMode) :
      WF p → LocallyFinite ⇑(den p) → WF (p.reflect m)

/-- Inversion: well-formedness of a reflect node yields the local finiteness
of the reflected subprogram. -/
theorem WF.reflect_locallyFinite {p : Prog α} {m : RMode}
    (h : WF (p.reflect m)) : LocallyFinite ⇑(den p) := by
  cases h with
  | reflect _ _ hlf => exact hlf

/-! ### The compiler -/

/-- `compile P = (I1, I2)` with `[[I1]] ∘ [[I2]] = [[P]]`, both involutions
(mirrors `compile_involutions`). -/
def compile (P : Prog α) : Prog α × Prog α :=
  (P.reflect .i1, P.reflect .i2)

/-- Both compiler outputs are well-formed whenever the source denotes a
locally finite map. -/
theorem compile_wf (P : Prog α) (hP : WF P) (h : LocallyFinite ⇑(den P)) :
    WF (compile P).1 ∧ WF (compile P).2 :=
  ⟨.reflect _ hP h, .reflect _ hP h⟩

/-- **Compiler correctness** (the `verify` loop, proved once and for all):
for locally finite `P`, `[[I1]] ∘ [[I2]] = [[P]]` pointwise.  Direct corollary
of `locallyFinite_eq_two_involutions`. -/
theorem compile_correct (P : Prog α) (h : LocallyFinite ⇑(den P)) :
    ∀ x, den (compile P).1 (den (compile P).2 x) = den P x := by
  intro x
  show den (P.reflect .i1) (den (P.reflect .i2) x) = den P x
  rw [den_reflect_i1 P h, den_reflect_i2 P h]
  exact (locallyFinite_eq_two_involutions h).2.2 x

/-- The first compiler output is an involution. -/
theorem compile_involutive₁ (P : Prog α) :
    IsInvolution ⇑(den (compile P).1) :=
  den_reflect_involutive P .i1

/-- The second compiler output is an involution. -/
theorem compile_involutive₂ (P : Prog α) :
    IsInvolution ⇑(den (compile P).2) :=
  den_reflect_involutive P .i2

/-- Packaged statement in the exact shape of
`locallyFinite_eq_two_involutions`, now about compiled *programs*. -/
theorem compile_spec (P : Prog α) (h : LocallyFinite ⇑(den P)) :
    IsInvolution ⇑(den (compile P).1) ∧ IsInvolution ⇑(den (compile P).2) ∧
      ∀ x, den (compile P).1 (den (compile P).2 x) = den P x :=
  ⟨compile_involutive₁ P, compile_involutive₂ P, compile_correct P h⟩

/-! ### Concrete example: the order-3 rotation on `Fin 3` (mirrors `rot_rgb`) -/

/-- `rot_rgb`: the order-3 rotation `s ↦ s + 1` on `Fin 3`, as a `prim`. -/
def rot : Prog (Fin 3) :=
  .prim (fun s => s + 1) (fun s => s - 1) (by decide) (by decide)

/-- `check_locally_finite rot`: every orbit closes in 3 steps
(machine-checked by `decide`). -/
theorem rot_locallyFinite : LocallyFinite ⇑(den rot) := by
  have h : ∀ x : Fin 3, (fun s : Fin 3 => s + 1)^[3] x = x := by decide
  exact fun x => ⟨3, by norm_num, h x⟩

theorem rot_wf : WF rot := .prim _ _ _ _

/-- `decide`-level sanity check of the source semantics. -/
example : den rot 0 = 1 ∧ den rot 1 = 2 ∧ den rot 2 = 0 := by
  refine ⟨rfl, rfl, rfl⟩

/-- The compiled pair composes back to the rotation, on every state. -/
example : ∀ x, den (compile rot).1 (den (compile rot).2 x) = den rot x :=
  compile_correct rot rot_locallyFinite

/-- ... and concretely at state `0` (`I1 (I2 0) = rot 0 = 1`). -/
example : den (compile rot).1 (den (compile rot).2 0) = 1 := by
  rw [compile_correct rot rot_locallyFinite]; rfl

/-- Both compiled programs are involutions. -/
example : IsInvolution ⇑(den (compile rot).1) ∧
    IsInvolution ⇑(den (compile rot).2) :=
  ⟨compile_involutive₁ rot, compile_involutive₂ rot⟩

end InvComp
end PeriodicTM
