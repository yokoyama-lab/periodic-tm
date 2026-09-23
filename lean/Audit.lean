/-
Axiom audit for the FiniteOrderTM development.

Run (from `lean/`):

    lake build            -- builds every module imported by FiniteOrderTM.lean
    lake env lean Audit.lean

Expected output: EVERY theorem listed below reports a subset of mathlib's
standard axioms

    [propext, Classical.choice, Quot.sound]

and nothing else.  In particular `sorryAx` must never appear (the library
contains no `sorry`: `grep -rn sorry FiniteOrderTM/` is empty) and
`Lean.ofReduceBool` must never appear here (no `native_decide` is used in
any module imported by `FiniteOrderTM.lean`).

The `native_decide` certificates of `FiniteOrderTM/QueryGame.lean` are
deliberately NOT imported from the root module (build time) and are audited
separately by `AuditQueryGame.lean`; those six theorems DO report
`Lean.ofReduceBool` in addition to the standard axioms — see that file and
`README.md`.

Coverage: one `#print axioms` per main theorem of every module in the
import list of `FiniteOrderTM.lean`, grouped by file in import order.  Every
name below was checked against the sources (namespace `PeriodicTM`, with
the sub-namespaces `PeriodicTM.InvComp`, `PeriodicTM.TwoPointCore`,
`PeriodicTM.Reverser`, `PeriodicTM.KernelDecomp`, `PeriodicTM.Doubling`,
`PeriodicTM.CenterExtraction` where indicated).
-/
import FiniteOrderTM

/-! ## Basic.lean — effective two-involution decomposition (finite order) -/
#print axioms PeriodicTM.finite_order_eq_two_involutions
#print axioms PeriodicTM.exists_two_involutions

/-! ## LocallyFinite.lean — Theorem 4.1 (pointwise periodic ⟹ two involutions) -/
#print axioms PeriodicTM.locallyFinite_eq_two_involutions
#print axioms PeriodicTM.exists_two_involutions_of_locallyFinite
#print axioms PeriodicTM.exists_two_involutions_of_orderDividing

/-! ## InvComp.lean — the involution compiler (deep embedding, `Perm` denotation) -/
#print axioms PeriodicTM.InvComp.den_bijective
#print axioms PeriodicTM.InvComp.compile_correct
#print axioms PeriodicTM.InvComp.compile_involutive₁
#print axioms PeriodicTM.InvComp.compile_involutive₂
#print axioms PeriodicTM.InvComp.compile_spec

/-! ## Dihedral.lean — inverse = same two involutions reversed; time symmetry -/
#print axioms PeriodicTM.exists_inverse_two_involutions
#print axioms PeriodicTM.finite_order_conjugate_to_inverse

/-! ## Machine.lean — single-tape (TM0) time reversal -/
#print axioms PeriodicTM.FlipOf.eval_rev
#print axioms PeriodicTM.tapeSem_inverse
#print axioms PeriodicTM.tapeSem_involutive_of_flip_equiv
#print axioms PeriodicTM.Involutory.tapeSem_involutive
#print axioms PeriodicTM.involutory_writeHead
#print axioms PeriodicTM.involution_of_involutory_writeHead

/-! ## Involutory.lean — syntactic involutivity, one-cell completeness -/
#print axioms PeriodicTM.SyntacticallyInvolutory.tapeSem_symm
#print axioms PeriodicTM.syntacticallyInvolutory_writeHead_iff
#print axioms PeriodicTM.tapeSem_writeHead
#print axioms PeriodicTM.completenessGoal_oneCell

/-! ## MultiTape.lean — k-tape model -/
#print axioms PeriodicTM.KFlipOf.eval_rev
#print axioms PeriodicTM.ktapeSem_inverse
#print axioms PeriodicTM.KInvolutory.ktapeSem_involutive
#print axioms PeriodicTM.involutory_bankSwap
#print axioms PeriodicTM.self_inverse_of_involutory_bankSwap
#print axioms PeriodicTM.involutory_chain

/-! ## PrePeriod.lean — pre-period one collapse `f = ι₁ ∘ ι₂ ∘ e` -/
#print axioms PeriodicTM.index_one_decomp

/-! ## Compose.lean / Lift.lean — combinators -/
#print axioms PeriodicTM.ktapeSem_seq
#print axioms PeriodicTM.ktapeSem_liftL

/-! ## Flip.lean — the flipped machine as an object -/
#print axioms PeriodicTM.KFlipOf.self_backdet
#print axioms PeriodicTM.flipM_tapeSem_inverse
#print axioms PeriodicTM.kFlipOf_liftL
#print axioms PeriodicTM.liftL_reversible
#print axioms PeriodicTM.liftL_halt_iff
#print axioms PeriodicTM.liftL_demand_iff

/-! ## Symmetrise.lean — flip distributes over `seq`; conjugation closure -/
#print axioms PeriodicTM.kFlipOf_seq
#print axioms PeriodicTM.conjSem
#print axioms PeriodicTM.conj_partial_involution
#print axioms PeriodicTM.conj_KInvolutory

/-! ## Completeness.lean — Nakano Thm 4.6 (machine-level symmetrisation) -/
#print axioms PeriodicTM.nakano_symmetrisation

/-! ## SemReversible.lean — semantic inverses (`SemInverse`) -/
#print axioms PeriodicTM.KReversible.semInverse
#print axioms PeriodicTM.SemInverse.injective
#print axioms PeriodicTM.conj_partial_involution_sem
#print axioms PeriodicTM.conj_partial_involution_of_KReversible
#print axioms PeriodicTM.SemInverse.seq
#print axioms PeriodicTM.SemInverse.liftL

/-! ## Reindex.lean — bank reindexing -/
#print axioms PeriodicTM.ktapeSem_renameBank
#print axioms PeriodicTM.SemInverse.renameBank

/-! ## Copy.lean / CopyMulti.lean / CopyMultiFold.lean / CopyMultiK.lean — copy machines -/
#print axioms PeriodicTM.copyM_semInverse
#print axioms PeriodicTM.copyStr_semInverse
#print axioms PeriodicTM.copyStrW_semInverse
#print axioms PeriodicTM.copyStrAt_semInverse
#print axioms PeriodicTM.haltMachine_semInverse
#print axioms PeriodicTM.copyPairs_semInverse
#print axioms PeriodicTM.copyMultiK_semInverse
#print axioms PeriodicTM.copyMultiK_preserves_left

/-! ## IOConvention.lean / IOConventionInstance.lean — string-level bridge -/
#print axioms PeriodicTM.readTape_left_irrelevant
#print axioms PeriodicTM.readTape_mk₁
#print axioms PeriodicTM.stringSem_involutive
#print axioms PeriodicTM.writeHead_stdOutput
#print axioms PeriodicTM.stringSem_writeHead_involutive

/-! ## InvolutoryString.lean — string involutions, closure (a), semantic closure (b) -/
#print axioms PeriodicTM.SyntacticallyInvolutory.stringInvolutory
#print axioms PeriodicTM.applyHead_involutive
#print axioms PeriodicTM.stringInvolutory_writeHead
#print axioms PeriodicTM.completenessGoal_oneCell_string
#print axioms PeriodicTM.conj_stringPartialInvolution

/-! ## InvolutoryTransport.lean — KMachine ⇔ TM0 transport -/
#print axioms PeriodicTM.ofK_toK
#print axioms PeriodicTM.tapeSem_ofK
#print axioms PeriodicTM.ktapeSem_toK
#print axioms PeriodicTM.Involutory.toK
#print axioms PeriodicTM.KInvolutory.ofK
#print axioms PeriodicTM.conj_syntacticallyInvolutory_ofK
#print axioms PeriodicTM.conjugationClosure_tapeSem
#print axioms PeriodicTM.conj_stringInvolutory_ofK

/-! ## InvolutoryBennett.lean — Bennett compute–copy–uncompute -/
#print axioms PeriodicTM.bennett_ktapeSem
#print axioms PeriodicTM.bennett_copyStr_mem
#print axioms PeriodicTM.writeK_reversible
#print axioms PeriodicTM.Reversibilisation.ofK_self
#print axioms PeriodicTM.reversibilisation_toK
#print axioms PeriodicTM.conjugationClosure_of_reversibilisation

/-! ## HistoryMachine.lean — history-logging simulator (unconditionally reversible) -/
#print axioms PeriodicTM.histM_reversible
#print axioms PeriodicTM.histM_respects
#print axioms PeriodicTM.histM_ktapeSem_proj
#print axioms PeriodicTM.histM_dom_iff

/-! ## InvolutoryAssembly.lean — StdOutput transport and assembly -/
#print axioms PeriodicTM.stringConjugationClosure_of_reversibilisation
#print axioms PeriodicTM.stringConjugationClosure_instance
#print axioms PeriodicTM.reversibilisation_writeHead
#print axioms PeriodicTM.stringConjugationClosure_applyHead

/-! ## NoGo.lean — pre-period-2 no-go (halting-tail encoding) -/
#print axioms PeriodicTM.range_idempotent_eq_fixpoints
#print axioms PeriodicTM.computablePred_fix_of_computable
#print axioms PeriodicTM.preperiod_two_nogo

/-! ## TwoPointCore.lean — Lemma 9.4 / Claim B / `k₁*` (symbolic core of Theorem 9.6) -/
#print axioms PeriodicTM.TwoPointCore.sameCycleValid_iff
#print axioms PeriodicTM.TwoPointCore.type3_universal
#print axioms PeriodicTM.TwoPointCore.type1_two_distances
#print axioms PeriodicTM.TwoPointCore.type2_two_distances
#print axioms PeriodicTM.TwoPointCore.type3_forces_eq
#print axioms PeriodicTM.TwoPointCore.type4_two_distances
#print axioms PeriodicTM.TwoPointCore.two_mul_injective_of_odd
#print axioms PeriodicTM.TwoPointCore.two_mul_succ_ne
#print axioms PeriodicTM.TwoPointCore.claimB_le_half
#print axioms PeriodicTM.TwoPointCore.kills_iff_minDivGe
#print axioms PeriodicTM.TwoPointCore.k1Star_mono
#print axioms PeriodicTM.TwoPointCore.reflection_eq_rho

/-! ## PermTwoInvolutions.lean — structural core of Theorem 7.3 (any permutation) -/
#print axioms PeriodicTM.Reverser.iota2_involution
#print axioms PeriodicTM.Reverser.iota1_involution
#print axioms PeriodicTM.Reverser.iota1_iota2
#print axioms PeriodicTM.Reverser.iota2_reverses
#print axioms PeriodicTM.perm_eq_two_involutions_of_rep
#print axioms PeriodicTM.perm_eq_two_involutions
#print axioms PeriodicTM.perm_strongly_reversible

/-! ## HalfShift.lean — Theorem 13.1 (half-shift correction) -/
#print axioms PeriodicTM.Reverser.halfShift_involution
#print axioms PeriodicTM.Reverser.halfShift_reverses
#print axioms PeriodicTM.half_shift_correction
#print axioms PeriodicTM.half_shift_correction_free
#print axioms PeriodicTM.strongly_reversible_iff_orbit_involutive_reverser

/-! ## CenterExtraction.lean — Lemma 7.1 and the abstract form of Theorem 7.2 -/
#print axioms PeriodicTM.CenterExtraction.exists_center
#print axioms PeriodicTM.CenterExtraction.center_unique
#print axioms PeriodicTM.CenterExtraction.centers_finite
#print axioms PeriodicTM.CenterExtraction.fixed_orbits_finite
#print axioms PeriodicTM.CenterExtraction.fixed_orbits_finite_of_computable

/-! ## Doubling.lean — Theorem 11.1 (mirror doubling) -/
#print axioms PeriodicTM.Doubling.iota_involutive
#print axioms PeriodicTM.Doubling.iota_reverses
#print axioms PeriodicTM.Doubling.not_sameCycle_iota
#print axioms PeriodicTM.Doubling.sameCycle_iff
#print axioms PeriodicTM.Doubling.free_double_iff
#print axioms PeriodicTM.Doubling.cycleImmune_double
#print axioms PeriodicTM.Doubling.computable_double
#print axioms PeriodicTM.Doubling.computable_iota
#print axioms PeriodicTM.mirror_doubling

/-! ## KernelDecomp.lean — Theorem 3.1 (kernel decomposition ⟺ decidable core) -/
#print axioms PeriodicTM.KernelDecomp.proj_idem
#print axioms PeriodicTM.KernelDecomp.range_proj
#print axioms PeriodicTM.KernelDecomp.core_period
#print axioms PeriodicTM.kernel_decomp_exists
#print axioms PeriodicTM.core_decidable_of_kernel_decomp
#print axioms PeriodicTM.three_factor_forces_indexOne
