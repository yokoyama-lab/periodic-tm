/-
FiniteOrderTM/Completeness2k.lean

#2 (2k-tape completeness): the SEMANTIC completeness corollary.

`Completeness.lean`'s `nakano_symmetrisation` mechanises Nakano Thm 4.6 at the
syntactic level: the 2k-tape symmetrisation of a `KReversible` k-tape machine `R₀`
is `KInvolutory`.  Here we cash that out semantically: the same 2k-tape machine
`D` computes a *partial involution* on its tape banks
(`IsPartialInvolution`, Unconditional.lean) — every output run reads back to its
input — via `KInvolutory.ktapeSem_involutive`.

This is the completeness *direction* (Axelsen–Glück Thm 3.12 / Nakano):
every involution that admits a `KReversible` realisation `R₀` is computed by a
machine whose semantics is involutive.  The ONE remaining gap to "every
computable involution" is producing that `R₀` from an arbitrary source — the
Bennett reversibilisation, which is unattainable syntactically over a shared
alphabet (`phaseF2_not_backdet`) and is achieved only on block data
semantically (`bennett_symmetrisation_conditional`).  So `hR₀rev : KReversible R₀`
is exactly the isolated hypothesis the full completeness theorem would have to
discharge; everything downstream of it is mechanised here.
-/
import FiniteOrderTM.Completeness
import FiniteOrderTM.Unconditional

namespace PeriodicTM

open Turing

variable {Γ : Type*} [Inhabited Γ] {Λ : Type*} {ι : Type*}

/-- **2k-tape semantic completeness (no `sorry`).**  Under the
`nakano_symmetrisation` hypotheses, the 2k-tape symmetrisation `D` of a
`KReversible` machine `R₀` computes a partial involution on its `ι ⊕ ι` tape
banks: the semantic companion of the syntactic `KInvolutory` result, obtained by
`KInvolutory.ktapeSem_involutive`.  The only hypothesis beyond the construction
is `hR₀rev`, isolating the Bennett-reversibilisation gap. -/
theorem nakano_completeness_semantic
    {σ : Λ → Λ} {q0 qf : Λ} {R₀ : KMachine Γ Λ ι}
    (hσ      : ∀ q, σ (σ q) = q)
    (hR₀rev  : KReversible R₀)
    (hR₀halt : ∀ q (a : ι → Γ), R₀ q a = none ↔ q = qf)
    (hR₀ent  : ∀ q (a : ι → Γ), (∃ v, Demand R₀ q a v) ↔ q ≠ q0) :
    IsPartialInvolution
      (seq (seq (liftL R₀ (κ := ι)) (bankSwap (Equiv.sumComm ι ι : Equiv.Perm (ι ⊕ ι)))
            false) (flipM (liftL R₀ (κ := ι)) σ) (σ qf))
      (Sum.inl (Sum.inl q0)) :=
  fun _ _ hY =>
    (nakano_symmetrisation hσ hR₀rev hR₀halt hR₀ent).ktapeSem_involutive hY

end PeriodicTM
