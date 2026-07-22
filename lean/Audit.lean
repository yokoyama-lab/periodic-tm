/-
Axiom audit for the FiniteOrderTM development.

Run:  lake env lean Audit.lean

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
-- #2: 2k-tape semantic completeness (KInvolutory → partial involution)
#print axioms PeriodicTM.nakano_completeness_semantic

-- I/O convention (M6c): tape-geometry lemmas and string-level bridge
-- readTape_left_irrelevant, readTape_mk₁, readTape_length: clean (Quot.sound)
-- stringSem_involutive: clean; depends on Involutory.tapeSem_involutive
#print axioms PeriodicTM.readTape_left_irrelevant
#print axioms PeriodicTM.readTape_mk₁
#print axioms PeriodicTM.stringSem_involutive
-- #4 follow-up: concrete StdOutput instance (writeHead g), string-level non-vacuity
#print axioms PeriodicTM.writeHead_stdOutput
#print axioms PeriodicTM.stringSem_writeHead_involutive

-- Section 7: reversibilisation (semantic) + full-string/multi-tape conjugation
-- (all clean; the FULLY unconditional goals bennett_reversibilization /
--  nakano_symmetrisation_unconditional / bennett_unconditional_target remain
--  documented `sorry`s and are deliberately not audited here)
#print axioms PeriodicTM.phaseF2_semInverse
#print axioms PeriodicTM.phaseF2_forward_correct
#print axioms PeriodicTM.bennettB_semInverse
#print axioms PeriodicTM.nakano_symmetrisation_unconditional_partial
#print axioms PeriodicTM.nakano_symmetrisation_headvalued
#print axioms PeriodicTM.bennettBStr_semInverse_blockdata
#print axioms PeriodicTM.bennettBStrK_semInverse_blockdata
#print axioms PeriodicTM.nakano_symmetrisation_strvalued
#print axioms PeriodicTM.nakano_symmetrisation_strvalued_K
#print axioms PeriodicTM.cellwiseM0_strvalued
#print axioms PeriodicTM.cellwiseM0_strvalued_K
#print axioms PeriodicTM.bennettBStrD_isPartialInvolutionOn
#print axioms PeriodicTM.bennettBStrKD_isPartialInvolutionOn
-- EXT-2 (2a): arbitrary finite data re-encodes to a block over Option Γ
#print axioms PeriodicTM.encodeStr_isBlock
-- EXT-2 (2c): arbitrary finite data is symmetrisable after re-encoding
#print axioms PeriodicTM.encodeStr_cellwise_symmetrisable
-- #1: the conditional symmetrisation target (the "unconditional wall" as a theorem)
#print axioms PeriodicTM.bennett_symmetrisation_conditional
#print axioms PeriodicTM.bennett_symmetrisation_conditional_K
#print axioms PeriodicTM.isPartialInvolutionOn_of_isPartialInvolution

-- Pre-period-2 no-go (A2/A3): all clean, no sorry
-- range_idempotent_eq_fixpoints: clean (propext, Quot.sound)
-- computablePred_fix_of_computable: clean (standard mathlib axioms)
-- preperiod_two_nogo: clean (halting-tail encoding, standard mathlib axioms)
#print axioms PeriodicTM.range_idempotent_eq_fixpoints
#print axioms PeriodicTM.computablePred_fix_of_computable
#print axioms PeriodicTM.preperiod_two_nogo
