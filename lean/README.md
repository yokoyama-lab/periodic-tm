# FiniteOrderTM — Lean 4 mechanisation

Lean 4 / mathlib mechanisation accompanying the paper *Involutory Turing
Machines, Formally* (and the companion theory paper on periodic Turing
machines). Namespace: `PeriodicTM`.

## Build

Requires [elan](https://github.com/leanprover/elan). The toolchain and
mathlib are pinned (`lean-toolchain`: v4.30.0; `lakefile.toml`:
mathlib tag v4.30.0).

```bash
lake exe cache get   # fetch prebuilt mathlib oleans (first time only)
lake build           # builds the whole development; no sorry
```

## Axiom audit

```bash
lake env lean Audit.lean
```

Every theorem reports a subset of mathlib's standard axioms
`[propext, Classical.choice, Quot.sound]`; `kFlipOf_seq`,
`KFlipOf.self_backdet`, `involutory_writeHead` (both directions) and
`self_inverse_of_involutory_bankSwap` need `propext` alone, and
`involutory_bankSwap` needs `propext` and `Quot.sound`.

## File map

| File | Contents |
|---|---|
| `FiniteOrderTM/Basic.lean` | Effective two-involution decomposition of finite-order bijections (`finite_order_eq_two_involutions`) |
| `FiniteOrderTM/LocallyFinite.lean` | Locally finite generalisation — every pointwise-periodic map is a product of two involutions (`locallyFinite_eq_two_involutions`; research note Theorem 4.1) |
| `FiniteOrderTM/PrePeriod.lean` | Pre-period-one collapse `f = ι₁ ∘ ι₂ ∘ e` (`index_one_decomp`) |
| `FiniteOrderTM/Machine.lean` | Single-tape (TM0) relational time-reversal: `FlipOf`, Lecerf reversal, inverse semantics, soundness; `writeHead` example |
| `FiniteOrderTM/MultiTape.lean` | k-tape model over an arbitrary tape-index type, with permutation rules; `KFlipOf`, `KInvolutory`, soundness; `bankSwap` (iff) and the `chain` independence example |
| `FiniteOrderTM/Compose.lean` | Sequential composition; hypothesis-free Kleisli semantics (`ktapeSem_seq`) |
| `FiniteOrderTM/Lift.lean` | Tape-bank lifting; hypothesis-free frame lemma (`ktapeSem_liftL`) |
| `FiniteOrderTM/Flip.lean` | The flipped machine as an object via the `Demand` predicate; `KReversible`; derived backward determinism (`KFlipOf.self_backdet`); `flipM_tapeSem_inverse` |
| `FiniteOrderTM/Symmetrise.lean` | Flip distributes over composition (`kFlipOf_seq`); conjugation closure, semantic form (`conj_partial_involution`) |
| `FiniteOrderTM/IOConvention.lean` | I/O convention (M6c): `readTape`, `StdOutput`, `stringSem`; bridge theorem `stringSem_involutive` (all clean, no sorry) |
| `FiniteOrderTM/NoGo.lean` | Pre-period-2 no-go (ROADMAP A2/A3): `range_idempotent_eq_fixpoints`, `computablePred_fix_of_computable`, `preperiod_two_nogo` via the halting-tail encoding (all clean, no sorry) |

Python prototypes for the decomposition theorems live one directory up
(`../finite_order.py`, `../preperiod.py`).
