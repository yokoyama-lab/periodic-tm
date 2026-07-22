/-
# Unconditional symmetrisation, function level (R1, Stage 0)

The documented goal `nakano_symmetrisation_unconditional` (Reversibilization.lean)
is stated in the WRONG shape: it asks for `KInvolutory` of the machine
`seq (seq (liftL M₀) bankSwap) (flipM (liftL M₀) σ)`, built from `M₀` through
`flipM`.  But `flipM` behaves as an inverse only for a `KReversible` machine,
and we proved no faithful Bennett simulator over a shared alphabet is
`KReversible` (`phaseF2_not_backdet`).  So that statement is unprovable in
general; it is not the right target.

The R2 bridge (`SemReversible.lean`) supplies the right target.  We split the
problem into two ORTHOGONAL gaps:

* **G1 (reversibility).**  Drop `KReversible`; replace `flipM` by a semantic
  inverse *machine* (the uncompute leg).  By `conj_partial_involution_sem` this
  reduces entirely to exhibiting that inverse leg.  The assembly is discharged
  here, with no `sorry`, as `conj_isPartialInvolution`.

* **G2 (correctness).**  The symmetrised machine actually computes `M₀`'s
  function.  This is independent and is OPEN even for the conditional theorem
  (the paper's `StdOutput` future-work item).

This file does Stage 0: it states `IsPartialInvolution`, proves the G1 assembly
against an arbitrary semantic inverse (no `sorry`), and records the corrected
final target `bennett_unconditional_target` as the single residual `sorry`
(Stages 1+3).  The old wrong-shape `sorry`s in Reversibilization.lean are kept
only as historical records of the original Track-B goal.
-/
import FiniteOrderTM.SemReversible

namespace PeriodicTM

open Turing

variable {Γ : Type*} [Inhabited Γ] {ι : Type*}

/-- A machine computes a partial involution from `q0`: every output run can be
read backwards as a run from the output to the input.  This is the semantic
conclusion of Nakano's symmetrisation, with no syntactic `KInvolutory`
requirement. -/
def IsPartialInvolution {Λ : Type*} (D : KMachine Γ Λ ι) (q0 : Λ) : Prop :=
  ∀ X Y, Y ∈ ktapeSem D q0 X → X ∈ ktapeSem D q0 Y

/-- A machine computes a partial involution on the input domain `DomIn`. -/
def IsPartialInvolutionOn {Λ : Type*} (D : KMachine Γ Λ ι) (q0 : Λ)
    (DomIn : (ι → Tape Γ) → Prop) : Prop :=
  ∀ X Y, DomIn X → Y ∈ ktapeSem D q0 X → X ∈ ktapeSem D q0 Y

variable {ΛR ΛR' ΛM : Type*}

/-- **G1 assembly (no `sorry`).**  The conjugate of an involutory machine `M`
by any reversibiliser `R` that admits a semantic inverse machine `R'` (`fwd` on
the input domain `DomIn`, `bwd` on the output domain `DomOut` which `M` maps
`R`-outputs into) computes a partial involution on `DomIn`.  No `KReversible`
hypothesis: the syntactic discipline is replaced by the domain-restricted
semantic inverse relation, the whole point of the R2 bridge. -/
theorem conj_isPartialInvolution
    {R : KMachine Γ ΛR ι} {R' : KMachine Γ ΛR' ι} {M : KMachine Γ ΛM ι}
    {σM : ΛM → ΛM} {q0R : ΛR} {q0R' : ΛR'} {q0M qfM : ΛM}
    {DomIn DomOut : (ι → Tape Γ) → Prop}
    (hM : KInvolutory M σM q0M qfM)
    (hinv : SemInverse R R' q0R q0R' DomIn DomOut)
    (hdom : ∀ U V, (∃ T, DomIn T ∧ U ∈ ktapeSem R q0R T) →
            V ∈ ktapeSem M q0M U → DomOut V) :
    IsPartialInvolutionOn (seq (seq R M q0M) R' q0R') (Sum.inl (Sum.inl q0R)) DomIn :=
  fun _ _ hT h => conj_partial_involution_sem hM hinv hdom hT h

/-- The conditional route recovered: a `KReversible` reversibiliser gives a
partial involution through its flip, with no extra work.  Sanity check that
`conj_isPartialInvolution` subsumes the original construction. -/
theorem conj_isPartialInvolution_of_KReversible
    {R : KMachine Γ ΛR ι} {M : KMachine Γ ΛM ι}
    {σR : ΛR → ΛR} {σM : ΛM → ΛM} {q0R qfR : ΛR} {q0M qfM : ΛM}
    (hM : KInvolutory M σM q0M qfM)
    (hσR : ∀ q, σR (σR q) = q) (hRrev : KReversible R)
    (hRhalt : ∀ q a, R q a = none ↔ q = qfR)
    (hRent : ∀ q b, (∃ v, Demand R q b v) ↔ q ≠ q0R) :
    IsPartialInvolution
      (seq (seq R M q0M) (flipM R σR) (σR qfR)) (Sum.inl (Sum.inl q0R)) :=
  fun X Y h => conj_isPartialInvolution hM (KReversible.semInverse hσR hRrev hRhalt hRent)
    (fun _ _ _ _ => trivial) X Y trivial h

variable {Λ : Type*}

/-- **Corrected final target (R1), PROVISIONAL `sorry`.**  For any machine `M₀`
computing a partial involution, there is a machine `D` (the Bennett-based
symmetrisation, over an extended alphabet `Γ'` and tape index `ι'`) that

* (G1) computes a partial involution -- no `KReversible` hypothesis; and
* (G2) simulates `M₀` under an encoding `enc` of the input tapes.

The proof will instantiate `conj_isPartialInvolution` with the Bennett
reversibiliser and its uncompute leg (Stage 1, for G1) and add forward
correctness (Stage 3, for G2).  The exact `Γ'`, `ι'`, `enc`, and the precise G2
relation are design choices fixed in Stage 1; the conjuncts below record intent
and will be refined there.  Replaces the wrong-shape
`nakano_symmetrisation_unconditional`. -/
theorem bennett_unconditional_target
    (M₀ : KMachine Γ Λ ι) (q₀ : Λ)
    (hInvol : IsPartialInvolution M₀ q₀) :
    ∃ (Λ' Γ' : Type*) (_ : Inhabited Γ') (ι' : Type*)
      (D : KMachine Γ' Λ' ι') (q0' : Λ')
      (enc : (ι → Tape Γ) → (ι' → Tape Γ')),
      IsPartialInvolution D q0' ∧
      (∀ T U, U ∈ ktapeSem M₀ q₀ T → enc U ∈ ktapeSem D q0' (enc T)) := by
  sorry

end PeriodicTM
