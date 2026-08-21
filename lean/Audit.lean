/-
Axiom audit for the FiniteOrderTM development.

Run:  plain `lake build` (this module is a default target, see
`lakefile.toml`), or `lake env lean Audit.lean` for the output alone.
It is a build target on purpose: from 2026-07-23 to 2026-08-21 this file
was orphaned and broken, and no gate noticed.

Expected output: every theorem reports a subset of
  [propext, Classical.choice, Quot.sound]
(mathlib's standard axioms).  `kFlipOf_seq`, `KFlipOf.self_backdet`,
`involutory_writeHead` (both directions) and
`self_inverse_of_involutory_bankSwap` need `propext` alone;
`involutory_bankSwap` needs `propext` and `Quot.sound`.

Theorems with `sorry` are marked below; all others are fully mechanised.
-/
import FiniteOrderTM

-- decomposition theory
#print axioms PeriodicTM.finite_order_eq_two_involutions
#print axioms PeriodicTM.index_one_decomp
-- #3: dihedral / ℤ-n symmetry (inverse = same two involutions reversed; time symmetry)
#print axioms PeriodicTM.exists_inverse_two_involutions
#print axioms PeriodicTM.finite_order_conjugate_to_inverse

-- single-tape machine theory (TM0)
#print axioms PeriodicTM.FlipOf.eval_rev
#print axioms PeriodicTM.tapeSem_inverse
#print axioms PeriodicTM.tapeSem_involutive_of_flip_equiv
#print axioms PeriodicTM.Involutory.tapeSem_involutive
#print axioms PeriodicTM.involutory_writeHead
#print axioms PeriodicTM.involution_of_involutory_writeHead

-- k-tape machine theory
#print axioms PeriodicTM.KFlipOf.eval_rev
#print axioms PeriodicTM.ktapeSem_inverse
#print axioms PeriodicTM.KInvolutory.ktapeSem_involutive
#print axioms PeriodicTM.involutory_bankSwap
#print axioms PeriodicTM.self_inverse_of_involutory_bankSwap
#print axioms PeriodicTM.involutory_chain

-- combinators
#print axioms PeriodicTM.ktapeSem_seq
#print axioms PeriodicTM.ktapeSem_liftL
#print axioms PeriodicTM.flipM_tapeSem_inverse
#print axioms PeriodicTM.KFlipOf.self_backdet
#print axioms PeriodicTM.kFlipOf_seq
#print axioms PeriodicTM.conjSem
#print axioms PeriodicTM.conj_partial_involution
#print axioms PeriodicTM.conj_KInvolutory
-- M7: machine-level completeness (Nakano Thm 4.6)
#print axioms PeriodicTM.kFlipOf_liftL
#print axioms PeriodicTM.liftL_halt_iff
#print axioms PeriodicTM.liftL_demand_iff
#print axioms PeriodicTM.nakano_symmetrisation
-- I/O convention (M6c): tape-geometry lemmas and string-level bridge
-- readTape_left_irrelevant, readTape_mk₁, readTape_length: clean (Quot.sound)
-- stringSem_involutive: clean; depends on Involutory.tapeSem_involutive
#print axioms PeriodicTM.readTape_left_irrelevant
#print axioms PeriodicTM.readTape_mk₁
#print axioms PeriodicTM.stringSem_involutive
-- #4 follow-up: concrete StdOutput instance (writeHead g), string-level non-vacuity
#print axioms PeriodicTM.writeHead_stdOutput
#print axioms PeriodicTM.stringSem_writeHead_involutive

-- Section 7 (reversibilisation) and EXT-2 (block re-encoding): 19
-- `#print axioms` lines used to sit here, naming declarations of the WIP
-- modules `Bennett*.lean` / `BlockEncode.lean` / `Completeness2k.lean` /
-- `Reversibilization.lean` / `Unconditional.lean`.  Those modules were
-- deleted in c1ec136 ("`sorry` を含む WIP Lean モジュールを除去",
-- 2026-07-23), about 20 minutes after this file was written, and the
-- lines were never updated — so this whole audit script has been
-- un-runnable ever since (19 "unknown constant" errors).  Nothing ran
-- it, so nobody noticed.  Removed 2026-08-21 together with wiring the
-- file into `lake build` (see `lakefile.toml`, target `Audit`).
-- The surviving successor results live in `SemReversible.lean` and
-- `InvolutoryBennett.lean`; re-adding entries for them is a separate
-- job for a human who knows which ones are the intended headline
-- theorems.

-- Pre-period-2 no-go (A2/A3): all clean, no sorry
-- range_idempotent_eq_fixpoints: clean (propext, Quot.sound)
-- computablePred_fix_of_computable: clean (standard mathlib axioms)
-- preperiod_two_nogo: clean (halting-tail encoding, standard mathlib axioms)
#print axioms PeriodicTM.range_idempotent_eq_fixpoints
#print axioms PeriodicTM.computablePred_fix_of_computable
#print axioms PeriodicTM.preperiod_two_nogo

-- Theorem 9.6: the exact value of the two-point consistency game
-- (research/09).  All clean: standard mathlib axioms, no `native_decide`.
-- `two_point_value` = lower bound (no depth-`q` tree wins for
-- `q < min (ℓ−2, k₁*)`) + upper bound (a depth-`min (ℓ−2, k₁*)` tree wins).
#print axioms PeriodicTM.Reflect.goodOutput_one_zero
#print axioms PeriodicTM.Reflect.goodOutput_cross
#print axioms PeriodicTM.Upper.goodOutput_pin
#print axioms PeriodicTM.Upper.walkZero_wins
#print axioms PeriodicTM.Upper.walkOne_wins
#print axioms PeriodicTM.ClaimA.two_point_lower_bound
#print axioms PeriodicTM.Upper.two_point_upper_bound
#print axioms PeriodicTM.Upper.two_point_value
-- `gameValue N ℓ = min (ℓ − 2) (k₁* N ℓ)` — the value formula itself.
#print axioms PeriodicTM.Upper.gameValue_eq
-- Regression check tying the Lean definition of `k₁*` to the exact-solver
-- table of `research/data/query_game_values.csv` (42 measured cells).
#print axioms PeriodicTM.Upper.closed_form_matches_measured

-- Layer-2 ONLY (bounded certification by compiled evaluation).  These
-- deliberately carry a `native_decide` axiom and must NOT be read as
-- clean: they are the mutation-injection probes showing the depth-2
-- winning trees of Theorem 9.6 lose when their leaf outputs are swapped.
#print axioms PeriodicTM.Upper.badPin_loses
#print axioms PeriodicTM.Upper.badKill_loses
