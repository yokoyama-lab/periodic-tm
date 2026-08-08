/-
WIP/ClaimAGeneral.lean — 主張A（補題9.7）一般証明の作業ファイル

root（FiniteOrderTM.lean）非取込・sorry 可の作業領域。完成した補題から
FiniteOrderTM/TwoPointClaimA.lean 本体へ移す。検査は
`lake env lean WIP/ClaimAGeneral.lean`（sorry は警告として残る）。

目標: `Statement N ℓ`（TwoPointClaimA.lean）
  ∀ s, s.Fits N → InLowerRegion N ℓ s →
    (FormulaSide N ℓ s ↔ CompletionSide N ℓ s)

分解（research/09 補題9.7 の証明の写し）:
* (⇒) completion_to_formula — 必要性。完成 f から m := 1 の軌道長を取る。
  - m ∣ ℓ            … orbit_card_dvd（本ファイルで証明済み）
  - m ≤ N − ℓ        … 0 の軌道（長さ ℓ）と 1 の軌道（長さ m）の非交差勘定
  - k₁ + 1 ≤ m       … P₁ の k₁+1 頂点が 1 の軌道に入る
  - q + r + 2 − ℓ ≤ m … 全パスが 2 軌道に入る場合の容量勘定＋第3軌道帰着
* (⇐) formula_to_completion — 十分性（パッキング構成）。約数 m を取り、
  0 のサイクル（長さ ℓ）と 1 のサイクル（長さ m）にパスを並べ、
  隙間を未開示点で埋め、残りを固定点にする。領域条件はここで効く
  （容量 ≥ 迷い総頂点、アトミック性の障害は未開示点で回避）。
-/
import FiniteOrderTM.TwoPointClaimA

namespace PeriodicTM.ClaimA

open Equiv Finset

/-! ## Leaf lemmas -/

/-- 位数条件 `f ^ ℓ = 1` の下で、任意の点の軌道長は `ℓ` を割る。
(⇒) の「m ∣ ℓ」を与える。 -/
theorem orbit_card_dvd {N ℓ : ℕ} (f : Perm (Fin N)) (hf : f ^ ℓ = 1)
    (x : Fin N) : #{y | f.SameCycle x y} ∣ ℓ := by
  by_cases hx : f x = x
  · have hiff : ∀ y, f.SameCycle x y ↔ y = x := fun y =>
      ⟨fun h => (h.eq_of_left hx).symm, by rintro rfl; exact Perm.SameCycle.refl f y⟩
    have hone : ({y | f.SameCycle x y} : Finset (Fin N)) = {x} := by
      ext y; simpa using hiff y
    rw [hone]
    simp
  · have hc : (f.cycleOf x).IsCycle := f.isCycle_cycleOf hx
    have hsupp : ({y | f.SameCycle x y} : Finset (Fin N)) =
        (f.cycleOf x).support := by
      ext y
      rw [Perm.mem_support_cycleOf_iff]
      simp [Perm.mem_support, hx]
    calc #{y | f.SameCycle x y}
        = #(f.cycleOf x).support := by rw [hsupp]
      _ = orderOf (f.cycleOf x) := hc.orderOf.symm
      _ ∣ orderOf f := f.orderOf_cycleOf_dvd_orderOf x
      _ ∣ ℓ := orderOf_dvd_of_pow_eq_one hf

/-- 異なる軌道は Finset として交わらない（(⇒) の `m ≤ N − ℓ` の勘定に使う）。 -/
theorem orbit_disjoint {N : ℕ} (f : Perm (Fin N)) {a b : Fin N}
    (hab : ¬ f.SameCycle a b) :
    Disjoint ({y | f.SameCycle a y} : Finset (Fin N))
      ({y | f.SameCycle b y} : Finset (Fin N)) := by
  rw [Finset.disjoint_left]
  intro y ha hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  exact hab (ha.trans hb.symm)

/-! ## 方向別の主定理（作業中） -/

/-- (⇒) 必要性: 別軌道完成が存在すれば式側の窓に約数が入る。
証人 m := 1 の軌道長。4 条件のうち m ∣ ℓ と非交差勘定は leaf 済み。 -/
theorem completion_to_formula {N ℓ : ℕ} [NeZero N] (s : AdvState)
    (hfit : s.Fits N) (hreg : InLowerRegion N ℓ s) (hℓ : 3 ≤ ℓ)
    (h : CompletionSide N ℓ s) : FormulaSide N ℓ s := by
  sorry

/-- (⇐) 十分性: 窓に約数 m があれば別軌道完成をパッキングで構成する。
research/09 の (⇐) の機械化。アトミック性の障害は領域条件
（未開示点の余裕）で回避する — 領域外では偽（Cert の cex）なので
仮定 `hreg` は落とせない。 -/
theorem formula_to_completion {N ℓ : ℕ} [NeZero N] (s : AdvState)
    (hfit : s.Fits N) (hreg : InLowerRegion N ℓ s) (hℓ : 3 ≤ ℓ)
    (h : FormulaSide N ℓ s) : CompletionSide N ℓ s := by
  sorry

/-- 主張A（一般形）: 2 方向の合成。 -/
theorem claimA_general {N ℓ : ℕ} [NeZero N] (hℓ : 3 ≤ ℓ) :
    ∀ s : AdvState, s.Fits N → InLowerRegion N ℓ s →
      (FormulaSide N ℓ s ↔ CompletionSide N ℓ s) :=
  fun s hfit hreg =>
    ⟨formula_to_completion s hfit hreg hℓ, completion_to_formula s hfit hreg hℓ⟩

end PeriodicTM.ClaimA
