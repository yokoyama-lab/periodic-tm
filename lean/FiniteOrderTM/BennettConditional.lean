/-
FiniteOrderTM/BennettConditional.lean

#1 (the "unconditional wall", made into a theorem).  The fully-unconditional
goal `bennett_unconditional_target` (Unconditional.lean) is a documented `sorry`.
It asks, for an ARBITRARY partial-involution `M₀`, for a machine `D` that

  (G1) is an UNRESTRICTED partial involution (`IsPartialInvolution D q0'`:
       *every* input to `D`, including non-encoded junk, runs back), and
  (G2) simulates `M₀` on ARBITRARY input data.

This file states and PROVES the conditional counterpart: under the two explicit
hypotheses that are exactly what the open goal lacks — `M₀` preserves blockness,
and we only claim the involution on the encoded block-data domain — the target
holds, assembled from the already-proven block machinery
(`bennettBStrD_isPartialInvolutionOn` for G1 restricted, `bennettBStrD_simulates`
for G2 on blocks).  So the open `sorry` is not a proof-engineering shortfall: the
gap is precisely (a) UNRESTRICTED vs domain-restricted involution, and (b)
arbitrary-data vs block-preserving simulation.

`isPartialInvolutionOn_of_isPartialInvolution` records (a) formally: the
conditional conclusion is genuinely WEAKER than the open goal's, so closing the
latter is strictly more than what we prove here.  The syntactic side of the same
wall is the separately-proven `phaseF2_not_backdet` (no shared-alphabet history
simulator is backward-deterministic).
-/
import FiniteOrderTM.Unconditional
import FiniteOrderTM.BennettStrConj

namespace PeriodicTM

open Turing

variable {Γ : Type*} [Inhabited Γ] [DecidableEq Γ] {ι : Type*}

/-- **The restricted conclusion is weaker than the unrestricted one.**  An
unrestricted partial involution is a partial involution on every domain.  So
`bennett_unconditional_target`'s `IsPartialInvolution` conjunct strictly implies
the domain-restricted `IsPartialInvolutionOn` we obtain below — the gap between
the open goal and the conditional theorem is real, not cosmetic. -/
theorem isPartialInvolutionOn_of_isPartialInvolution {Λ' : Type*}
    {D : KMachine Γ Λ' ι} {q0 : Λ'} (Dom : (ι → Tape Γ) → Prop)
    (h : IsPartialInvolution D q0) : IsPartialInvolutionOn D q0 Dom :=
  fun X Y _ hY => h X Y hY

variable {Λ : Type*} [DecidableEq Λ]

/-- **#1: the conditional symmetrisation target (no `sorry`).**  For any `M₀`
computing a partial involution (`hInvol`) that *preserves blockness* (`hblk`),
the full-string Bennett involution `D = bennettBStrD M₀ q₀` and the encoding
`enc A = (liftWork A, blank ancilla)` satisfy the `bennett_unconditional_target`
conclusion **on the block-data domain**:

* (G1) `D` is a partial involution on the encoded block points `Dom`
  (`bennettBStrD_isPartialInvolutionOn`); and
* (G2) `D` simulates `M₀` on every block input, and the encoded input lands in
  `Dom` (`bennettBStrD_simulates`).

This is the honest form of the open goal: the two hypotheses `hblk` and the
restriction to `Dom` are exactly what the fully-unconditional `sorry` would have
to remove.  An arbitrary `M₀` may write into the ancilla padding and break
blockness, so dropping `hblk` is not available from this construction.  (Stated
about the concrete `D`/`q0'`; the open goal quantifies the carrier types
existentially, which `D` instantiates.) -/
theorem bennett_symmetrisation_conditional
    (M₀ : KMachine Γ Λ Unit) (q₀ : Λ)
    (hInvol : IsPartialInvolution M₀ q₀)
    (hblk : ∀ X Y, (∀ j, IsBlock (X j)) → Y ∈ ktapeSem M₀ q₀ X → ∀ j, IsBlock (Y j)) :
    ∃ (enc : (Unit → Tape Γ) →
          ((Unit ⊕ Fin 1) ⊕ Unit → Tape (BennettAlph2 Γ Λ Unit)))
      (Dom : ((Unit ⊕ Fin 1) ⊕ Unit → Tape (BennettAlph2 Γ Λ Unit)) → Prop),
      IsPartialInvolutionOn (bennettBStrD M₀ q₀)
          (Sum.inl (Sum.inl (Sum.inl (Sum.inl (BennettState2.A1 q₀))))) Dom ∧
      (∀ A U, (∀ j, IsBlock (A j)) → U ∈ ktapeSem M₀ q₀ A →
        Dom (enc A) ∧ enc U ∈ ktapeSem (bennettBStrD M₀ q₀)
          (Sum.inl (Sum.inl (Sum.inl (Sum.inl (BennettState2.A1 q₀))))) (enc A)) := by
  refine ⟨(fun A => withR (fun _ : Unit => (default : Tape (BennettAlph2 Γ Λ Unit)))
      (liftWork M₀ A)),
    (fun X => ∃ A U, (∀ j, IsBlock (A j)) ∧ (∀ j, IsBlock (U j)) ∧
      U ∈ ktapeSem M₀ q₀ A ∧ A ∈ ktapeSem M₀ q₀ U ∧
      X = withR (fun _ : Unit => (default : Tape (BennettAlph2 Γ Λ Unit)))
        (liftWork M₀ A)),
    bennettBStrD_isPartialInvolutionOn M₀ q₀, ?_⟩
  intro A U hA hAU
  have hU : ∀ j, IsBlock (U j) := hblk A U hA hAU
  have hUA : A ∈ ktapeSem M₀ q₀ U := hInvol A U hAU
  exact ⟨⟨A, U, hA, hU, hAU, hUA, rfl⟩,
         bennettBStrD_simulates M₀ q₀ A U hA hU hAU hUA⟩

/-- **#1, multi-tape.**  The `k`-tape conditional symmetrisation target, assembled
from `bennettBStrKD_isPartialInvolutionOn` and `bennettBStrKD_simulates`. -/
theorem bennett_symmetrisation_conditional_K
    (k : ℕ) (M₀ : KMachine Γ Λ (Fin k)) (q₀ : Λ)
    (hInvol : IsPartialInvolution M₀ q₀)
    (hblk : ∀ X Y, (∀ j, IsBlock (X j)) → Y ∈ ktapeSem M₀ q₀ X → ∀ j, IsBlock (Y j)) :
    ∃ (enc : (Fin k → Tape Γ) →
          ((Fin k ⊕ Fin 1) ⊕ Fin k → Tape (BennettAlph2 Γ Λ (Fin k))))
      (Dom : ((Fin k ⊕ Fin 1) ⊕ Fin k → Tape (BennettAlph2 Γ Λ (Fin k))) → Prop),
      IsPartialInvolutionOn (bennettBStrKD k M₀ q₀)
          (Sum.inl (Sum.inl (Sum.inl (Sum.inl (BennettState2.A1 q₀))))) Dom ∧
      (∀ A U, (∀ j, IsBlock (A j)) → U ∈ ktapeSem M₀ q₀ A →
        Dom (enc A) ∧ enc U ∈ ktapeSem (bennettBStrKD k M₀ q₀)
          (Sum.inl (Sum.inl (Sum.inl (Sum.inl (BennettState2.A1 q₀))))) (enc A)) := by
  refine ⟨(fun A => withR (fun _ : Fin k => (default : Tape (BennettAlph2 Γ Λ (Fin k))))
      (liftWork M₀ A)),
    (fun X => ∃ A U, (∀ j, IsBlock (A j)) ∧ (∀ j, IsBlock (U j)) ∧
      U ∈ ktapeSem M₀ q₀ A ∧ A ∈ ktapeSem M₀ q₀ U ∧
      X = withR (fun _ : Fin k => (default : Tape (BennettAlph2 Γ Λ (Fin k))))
        (liftWork M₀ A)),
    bennettBStrKD_isPartialInvolutionOn k M₀ q₀, ?_⟩
  intro A U hA hAU
  have hU : ∀ j, IsBlock (U j) := hblk A U hA hAU
  have hUA : A ∈ ktapeSem M₀ q₀ U := hInvol A U hAU
  exact ⟨⟨A, U, hA, hU, hAU, hUA, rfl⟩,
         bennettBStrKD_simulates k M₀ q₀ A U hA hU hAU hUA⟩

end PeriodicTM
