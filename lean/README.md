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
lake env lean Audit.lean            # main library (every module imported by FiniteOrderTM.lean)
lake build FiniteOrderTM.QueryGame  # optional: the native_decide certificates (slow)
lake env lean AuditQueryGame.lean
```

`Audit.lean` prints the axioms of one representative theorem per main
result of every module in the import list of `FiniteOrderTM.lean`, grouped
by file.  Every one of them must report a subset of mathlib's standard
axioms `[propext, Classical.choice, Quot.sound]`; `sorryAx` never appears
(there is no `sorry` in the development) and neither does
`Lean.ofReduceBool` (no `native_decide` in the main library).

`AuditQueryGame.lean` audits `FiniteOrderTM/QueryGame.lean`, which is *not*
imported from the root module because its certificates are slow to compile.
Its two general lemmas are clean; its six bounded certificates (the "small
game values" row of `research/STATUS.md`) are proved by `native_decide` and
therefore additionally report **`Lean.ofReduceBool`**, i.e. they trust the
compiled evaluation of the decision procedure.  The reduction from "all
adaptive strategies" to that executable check is the ordinary theorem
`winnableB_iff_exists_tree`.

The GitHub Actions workflow `.github/workflows/lean-ci.yml` runs both audits.

## File map

Modules imported by `FiniteOrderTM.lean` (built by `lake build`), in import order:

| File | Contents |
|---|---|
| `FiniteOrderTM/Basic.lean` | Effective two-involution decomposition of finite-order bijections (`finite_order_eq_two_involutions`) |
| `FiniteOrderTM/LocallyFinite.lean` | Locally finite generalisation — every pointwise-periodic map is a product of two involutions (`locallyFinite_eq_two_involutions`; research note Theorem 4.1) |
| `FiniteOrderTM/InvComp.lean` | The involution compiler (mirror of `../invcomp/invcomp.py`), deep embedding with `Perm` denotation; `compile_correct`, `compile_involutive₁/₂`, `compile_spec` |
| `FiniteOrderTM/Dihedral.lean` | The inverse decomposes with the same two involutions reversed; time symmetry via an involution (`exists_inverse_two_involutions`, `finite_order_conjugate_to_inverse`) |
| `FiniteOrderTM/Machine.lean` | Single-tape (TM0) relational time-reversal: `FlipOf`, Lecerf reversal, inverse semantics, soundness; `writeHead` example |
| `FiniteOrderTM/Involutory.lean` | Syntactic involutivity (`SyntacticallyInvolutory`), `writeHead` iff, one-cell completeness (`completenessGoal_oneCell`) |
| `FiniteOrderTM/MultiTape.lean` | k-tape model over an arbitrary tape-index type, with permutation rules; `KFlipOf`, `KInvolutory`, soundness; `bankSwap` (iff) and the `chain` independence example |
| `FiniteOrderTM/PrePeriod.lean` | Pre-period-one collapse `f = ι₁ ∘ ι₂ ∘ e` (`index_one_decomp`) |
| `FiniteOrderTM/Compose.lean` | Sequential composition; hypothesis-free Kleisli semantics (`ktapeSem_seq`) |
| `FiniteOrderTM/Lift.lean` | Tape-bank lifting; hypothesis-free frame lemma (`ktapeSem_liftL`) |
| `FiniteOrderTM/Flip.lean` | The flipped machine as an object via the `Demand` predicate; `KReversible`; derived backward determinism (`KFlipOf.self_backdet`); `flipM_tapeSem_inverse`; `liftL_reversible` |
| `FiniteOrderTM/Symmetrise.lean` | Flip distributes over composition (`kFlipOf_seq`); conjugation closure, syntactic and semantic (`conj_KInvolutory`, `conj_partial_involution`) |
| `FiniteOrderTM/Completeness.lean` | Machine-level completeness, Nakano Thm 4.6 (`nakano_symmetrisation`) |
| `FiniteOrderTM/SemReversible.lean` | Semantic inverses `SemInverse` (domain-gated), decoupling symmetrisation from `KReversible` (`conj_partial_involution_sem`) |
| `FiniteOrderTM/Reindex.lean` | Bank reindexing along `ι ≃ ι'` (`ktapeSem_renameBank`, `SemInverse.renameBank`) |
| `FiniteOrderTM/Copy.lean` | Single-cell and full-string copy machines with semantic inverses (`copyM_semInverse`, `copyStr_semInverse`, `copyStrW_semInverse`) |
| `FiniteOrderTM/CopyMulti.lean` | Copy at a selected pair of banks, frozen others (`copyStrAt_semInverse`, `haltMachine_semInverse`) |
| `FiniteOrderTM/CopyMultiFold.lean` | Fold of per-pair copies is semantically reversible (`copyPairs_semInverse`) |
| `FiniteOrderTM/CopyMultiK.lean` | `Fin k` specialisation: copy every work tape onto its ancilla (`copyMultiK_semInverse`) |
| `FiniteOrderTM/IOConvention.lean` | I/O convention (M6c): `readTape`, `StdOutput`, `stringSem`; bridge theorem `stringSem_involutive` |
| `FiniteOrderTM/IOConventionInstance.lean` | Concrete `StdOutput` instance for `writeHead` (`writeHead_stdOutput`, `stringSem_writeHead_involutive`) |
| `FiniteOrderTM/InvolutoryString.lean` | String-level involutions: `StringInvolutory`, closure (a), `applyHead`, semantic conjugation closure (`conj_stringPartialInvolution`) |
| `FiniteOrderTM/InvolutoryTransport.lean` | KMachine ⇔ TM0 transport (`ofK`/`toK` bisimulation), syntactic transport, machine-level conjugation closure (`conjugationClosure_tapeSem`) |
| `FiniteOrderTM/InvolutoryBennett.lean` | Bennett compute–copy–uncompute composite (`bennett_ktapeSem`), `writeK` family, `Reversibilisation` interface |
| `FiniteOrderTM/HistoryMachine.lean` | History-logging simulator of an arbitrary k-tape machine, unconditionally `KReversible` (`histM_reversible`, `histM_ktapeSem_proj`) |
| `FiniteOrderTM/InvolutoryAssembly.lean` | `StdOutput` transport under Kleisli composition and the string-level assembly (`stringConjugationClosure_of_reversibilisation`, `stringConjugationClosure_applyHead`) |
| `FiniteOrderTM/NoGo.lean` | Pre-period-2 no-go (ROADMAP A2/A3): `range_idempotent_eq_fixpoints`, `computablePred_fix_of_computable`, `preperiod_two_nogo` via the halting-tail encoding |
| `FiniteOrderTM/TwoPointCore.lean` | Symbolic core of the two-point query-game value formula (research note Theorem 9.6): Lemma 9.4 on `ZMod ℓ`, Claim B arithmetic, `k₁*`, reflection rigidity |
| `FiniteOrderTM/PermTwoInvolutions.lean` | Structural core of Theorem 7.3: from any orbit datum (representatives + positions) an arbitrary permutation is `ι₁ ∘ ι₂` (`perm_eq_two_involutions_of_rep`); classically every permutation is a product of two involutions and strongly reversible |
| `FiniteOrderTM/HalfShift.lean` | Theorem 13.1 (half-shift correction): a reverser with involutive orbit action yields an explicit involutive reverser (`half_shift_correction`, `half_shift_correction_free`); 問B characterisation on free permutations |
| `FiniteOrderTM/KernelDecomp.lean` | Theorem 3.1 (kernel decomposition ⟺ decidable core): structural (i)⟹(ii) `kernel_decomp_exists`, full (ii)⟹(i) `core_decidable_of_kernel_decomp`, Observation 3.0 `three_factor_forces_indexOne` |
| `FiniteOrderTM/Doubling.lean` | Theorem 11.1 (mirror doubling): `double ρ` on `β × Bool`, the face swap as a computable involutive reverser fixing no cycle, inheritance of cycle-immunity (`mirror_doubling`) |
| `FiniteOrderTM/CenterExtraction.lean` | Lemma 7.1 (centre extraction, `exists_center`) and the abstract form of Theorem 7.2: a computable reverser of a free cycle-immune permutation fixes finitely many orbits (`fixed_orbits_finite_of_computable`) |

Modules **not** imported by `FiniteOrderTM.lean`:

| File | Contents |
|---|---|
| `FiniteOrderTM/QueryGame.lean` | Machine-checked certificates for the two-point query game: general lemmas (`winnableB_iff_exists_tree`) and `native_decide` values for small `(N, ℓ)`; build with `lake build FiniteOrderTM.QueryGame`, audit with `AuditQueryGame.lean` (uses `Lean.ofReduceBool`) |
| `FiniteOrderTM/EventuallyPeriodic.lean` | Standalone mathlib-style file on eventually-periodic points (`Function.IsEventuallyPeriodicPt`, `idempotentExp`); not referenced by the rest of the development and not built by `lake build` |

Python prototypes for the decomposition theorems live one directory up
(`../finite_order.py`, `../preperiod.py`).
