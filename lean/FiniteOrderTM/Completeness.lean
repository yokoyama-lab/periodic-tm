/-
FiniteOrderTM/Completeness.lean

Track B, milestone M7: machine-level completeness (Nakano Thm 4.6).

Given a `KReversible` k-tape TM R₀ computing an involution, the
2k-tape symmetrisation

  D = seq (seq (liftL R₀) (bankSwap swap) false)
          (flipM (liftL R₀) σ) (σ qf)

is `KInvolutory`.  The proof is a direct application of `conj_KInvolutory`
(Symmetrise.lean) using `liftL_reversible`, `liftL_halt_iff`, and
`liftL_demand_iff` (Flip.lean) and `involutory_bankSwap` (MultiTape.lean).

The "every computable involution" form (Axelsen–Glück Thm 3.12 / Bennett
reversibilisation) is kept as a hypothesis `hR₀rev : KReversible R₀` and
is not mechanised here (Track B M8).
-/
import FiniteOrderTM.Symmetrise

namespace PeriodicTM

open Turing

variable {Γ : Type*} [Inhabited Γ]
variable {Λ : Type*}
variable {ι : Type*}

/-! ### Nakano Thm 4.6 — 2k-tape symmetrisation is KInvolutory -/

/-- The 2k-tape symmetrisation of a reversible k-tape machine is KInvolutory.

Given:
* `R₀ : KMachine Γ Λ ι` — the original k-tape machine (each bank has type `ι`)
* `σ : Λ → Λ` — involutive state bijection with `σ q₀ = qf`
* `hR₀rev` — syntactic reversibility of R₀
* `hR₀halt` — unique-halt condition
* `hR₀ent` — entry condition (all non-initial states have a predecessor)

The output machine operates on `ι ⊕ ι` tapes (left bank + right bank),
with state type `(Λ ⊕ Bool) ⊕ Λ`. -/
theorem nakano_symmetrisation
    {σ : Λ → Λ} {q0 qf : Λ}
    {R₀ : KMachine Γ Λ ι}
    (hσ      : ∀ q, σ (σ q) = q)
    (hR₀rev  : KReversible R₀)
    (hR₀halt : ∀ q (a : ι → Γ), R₀ q a = none ↔ q = qf)
    (hR₀ent  : ∀ q (a : ι → Γ), (∃ v, Demand R₀ q a v) ↔ q ≠ q0) :
    let R    := liftL R₀ (κ := ι)
    let swap := (Equiv.sumComm ι ι : Equiv.Perm (ι ⊕ ι))
    KInvolutory
      (seq (seq R (bankSwap swap) false) (flipM R σ) (σ qf))
      (conjσ σ not)
      (Sum.inl (Sum.inl q0))
      (Sum.inr (σ q0)) :=
  conj_KInvolutory
    (hM     := involutory_bankSwap _ (Equiv.sumComm_symm ι ι))
    (hσR    := hσ)
    (hRrev  := liftL_reversible hR₀rev)
    (hRhalt := liftL_halt_iff hR₀halt)
    (hRent  := liftL_demand_iff hR₀ent)

end PeriodicTM
