/-
Axiom audit for the `native_decide` certificates of
`FiniteOrderTM/QueryGame.lean` (kept out of `Audit.lean` and out of the root
module because their compiled evaluation is slow).

Run (from `lean/`):

    lake build FiniteOrderTM.QueryGame
    lake env lean AuditQueryGame.lean

Expected output:

* the two general (Layer-1) lemmas report a subset of
  `[propext, Classical.choice, Quot.sound]`;
* the six bounded certificates ADDITIONALLY report `Lean.ofReduceBool`:
  they are proved by `native_decide`, i.e. by trusting the compiled
  evaluation of the decision procedures (`winnableB`, `GoodOutput`).  The
  reduction from "all adaptive depth-`q` strategies" to that executable
  check is the fully proved lemma `winnableB_iff_exists_tree`; only the
  evaluation itself is delegated to the compiler.  This is an honest
  strengthening of the trust base and is recorded as such in
  `research/STATUS.md` ("ゲーム値の小例" row).
-/
import FiniteOrderTM.QueryGame

-- Layer 1: general lemmas (standard axioms only)
#print axioms PeriodicTM.QueryGame.goodOutput_iff_perm
#print axioms PeriodicTM.QueryGame.winnableB_iff_exists_tree

-- Layer 2: bounded certificates (expected to include `Lean.ofReduceBool`)
#print axioms PeriodicTM.QueryGame.no_depth0_N5_n3_l3
#print axioms PeriodicTM.QueryGame.treeN5_wins
#print axioms PeriodicTM.QueryGame.value_eq_one_N5_n3_l3
#print axioms PeriodicTM.QueryGame.no_depth1_N6_n4_l4
#print axioms PeriodicTM.QueryGame.exists_depth2_N6_n4_l4
#print axioms PeriodicTM.QueryGame.no_depth1_N7_n4_l4
