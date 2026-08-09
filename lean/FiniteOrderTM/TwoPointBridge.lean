/-
FiniteOrderTM/TwoPointBridge.lean
— 抽象側（`TwoPointCore` の `ZMod ℓ` 座標）と具体側（`QueryGame` の
`Perm (Fin N)`）の橋渡し。定理9.6 の roadmap ステップ1・2にあたる。

方針: 長さ `ℓ` のサイクル上では、`f` の反復が位置座標
`ZMod ℓ` と一対一に対応する（`pow_apply_eq_iff`）。これを土台に
`QueryGame.GoodOutput` を `TwoPointCore.SameCycleValid` へ移す。

**BUILD NOTE**: root（`FiniteOrderTM.lean`）非取込。検査は
`lake env lean FiniteOrderTM/TwoPointBridge.lean`。
-/
import FiniteOrderTM.TwoPointCore

namespace PeriodicTM.TwoPointBridge

open Equiv Finset

variable {N : ℕ}

/-- 固定点では反復は動かない。 -/
theorem pow_apply_of_fixed {f : Perm (Fin N)} {x : Fin N} (hx : f x = x) :
    ∀ n : ℕ, (f ^ n) x = x := by
  intro n
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, Perm.mul_apply, hx, ih]

/-- 軌道が単元集合になるのは固定点のとき。 -/
theorem orbit_eq_singleton {f : Perm (Fin N)} {x : Fin N} (hx : f x = x) :
    ({y | f.SameCycle x y} : Finset (Fin N)) = {x} := by
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact ⟨fun h => (h.eq_of_left hx).symm, by rintro rfl; exact Perm.SameCycle.refl f y⟩

/-- 非固定点の軌道は `cycleOf` の台。 -/
theorem orbit_eq_support {f : Perm (Fin N)} {x : Fin N} (hx : f x ≠ x) :
    ({y | f.SameCycle x y} : Finset (Fin N)) = (f.cycleOf x).support := by
  ext y
  rw [Perm.mem_support_cycleOf_iff]
  simp [Perm.mem_support, hx]

/-- **位置座標の核**: 軌道長が `ℓ` の点 `x` では、`f` の反復が
`ZMod ℓ` の元と一対一に対応する。
`f^i x = f^j x ↔ (i : ZMod ℓ) = j`。

これが `TwoPointCore` の `ZMod ℓ` 上の型分類（補題9.4）を
具体的な `QueryGame` の設定へ移すための土台になる。 -/
theorem pow_apply_eq_iff {ℓ : ℕ} (f : Perm (Fin N)) (x : Fin N)
    (hcard : #{y | f.SameCycle x y} = ℓ) {i j : ℕ} :
    (f ^ i) x = (f ^ j) x ↔ (i : ZMod ℓ) = (j : ZMod ℓ) := by
  rw [ZMod.natCast_eq_natCast_iff]
  by_cases hx : f x = x
  · -- 固定点: 軌道長は 1、両辺とも恒真
    have hl : ℓ = 1 := by
      rw [← hcard, orbit_eq_singleton hx]; simp
    subst hl
    constructor
    · intro _; exact Nat.modEq_one
    · intro _; rw [pow_apply_of_fixed hx, pow_apply_of_fixed hx]
  · have hmem : x ∈ (f.cycleOf x).support := by
      rw [Perm.mem_support, Perm.cycleOf_apply_self]
      exact hx
    have hkey := (f.isCycleOn_support_cycleOf x).pow_apply_eq_pow_apply hmem
      (m := i) (n := j)
    rw [← hcard, orbit_eq_support hx]
    exact hkey

/-- 系: `f^i x = x ↔ ℓ ∣ i`（位置 0 に戻る条件）。 -/
theorem pow_apply_eq_self_iff {ℓ : ℕ} (f : Perm (Fin N)) (x : Fin N)
    (hcard : #{y | f.SameCycle x y} = ℓ) {i : ℕ} :
    (f ^ i) x = x ↔ (i : ZMod ℓ) = 0 := by
  have h := pow_apply_eq_iff (ℓ := ℓ) f x hcard (i := i) (j := 0)
  simpa using h

end PeriodicTM.TwoPointBridge

#print axioms PeriodicTM.TwoPointBridge.pow_apply_eq_iff
