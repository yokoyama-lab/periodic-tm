/-
FiniteOrderTM/TwoPointReflect.lean
— 軌道保存反射の存在（定理9.6 上界・roadmap ステップ6 の部品）

上界の勝利木の葉では「この出力対が良い」ことを示す必要があり、
それには任意の許容オラクル `f` に対する**有効反射の構成**が要る
（下界は反射の性質だけ使ったが、上界は存在を使う）。

構成は `LocallyFinite.lean` の `LF.iota2`（各軌道を基点で反転する
対合、対合性は証明済み）を基準反射とし、
* `IsReflection f (refl0 f)`（軌道保存と `f∘ι` の対合性を接続）、
* シフト族 `z ↦ f^k (ι z)` も反射（`isReflection_pow_comp`）、
* 軌道ごとのシフト `z ↦ f^(shift z) (ι z)`（`shift` は軌道不変）も反射、
から
* 同一軌道なら `(1, 0)` が良い出力（`goodOutput_one_zero`）、
* 別軌道なら `v₀ ∈ O(0)`・`v₁ ∈ O(1)` の任意の対が良い出力
  （`goodOutput_cross`）
を得る。これらが上界の 2 つの勝ち筋（別軌道殺し・d ピン留め）の
葉の証明の土台になる。

**BUILD NOTE**: root（`FiniteOrderTM.lean`）非取込。検査は
`lake env lean FiniteOrderTM/TwoPointReflect.lean`。
-/
import FiniteOrderTM.QueryGame
import FiniteOrderTM.LocallyFinite
import FiniteOrderTM.TwoPointBridge

namespace PeriodicTM.Reflect

open Equiv
open PeriodicTM.QueryGame (GoodOutput IsReflection)

variable {N : ℕ} [NeZero N]

noncomputable section

/-- 有限型の置換は局所有限。 -/
theorem perm_locallyFinite (f : Perm (Fin N)) :
    PeriodicTM.LocallyFinite ⇑f := by
  intro x
  refine ⟨orderOf f, orderOf_pos f, ?_⟩
  rw [← Equiv.Perm.coe_pow, pow_orderOf_eq_one]
  rfl

/-- 基準反射: 各軌道を基点で反転する（`LF.iota2`）。 -/
def refl0 (f : Perm (Fin N)) : Fin N → Fin N :=
  PeriodicTM.LF.iota2 ⇑f (perm_locallyFinite f)

/-- 基準反射は有効反射。対合性と `f∘ι` の対合性は
`LF.iota2_involution` / `LF.iota1_involution`、軌道保存は
基点への往復から。 -/
theorem refl0_isReflection (f : Perm (Fin N)) :
    IsReflection f (refl0 f) := by
  refine ⟨PeriodicTM.LF.iota2_involution (perm_locallyFinite f), ?_, ?_⟩
  · intro x
    have h1 : (⇑f)^[PeriodicTM.LF.pos ⇑f (perm_locallyFinite f) x]
        (PeriodicTM.LF.rep ⇑f (perm_locallyFinite f) x) = x :=
      PeriodicTM.LF.pos_spec (perm_locallyFinite f) x
    have hrx : f.SameCycle
        (PeriodicTM.LF.rep ⇑f (perm_locallyFinite f) x) x := by
      refine ⟨(PeriodicTM.LF.pos ⇑f (perm_locallyFinite f) x : ℤ), ?_⟩
      rw [zpow_natCast, Equiv.Perm.coe_pow]
      exact h1
    have hrr : f.SameCycle
        (PeriodicTM.LF.rep ⇑f (perm_locallyFinite f) x) (refl0 f x) := by
      refine ⟨((PeriodicTM.LF.per ⇑f (perm_locallyFinite f) x
        - PeriodicTM.LF.pos ⇑f (perm_locallyFinite f) x : ℕ) : ℤ), ?_⟩
      rw [zpow_natCast, Equiv.Perm.coe_pow]
      rfl
    exact hrx.symm.trans hrr
  · intro x
    have h := PeriodicTM.LF.iota1_involution (perm_locallyFinite f) x
    simpa [PeriodicTM.LF.iota1, refl0] using h

/-- 反射を `f^k` でずらしても反射。 -/
theorem isReflection_pow_comp {f : Perm (Fin N)} {ι : Fin N → Fin N}
    (h : IsReflection f ι) (k : ℕ) :
    IsReflection f (fun z => (f ^ k) (ι z)) := by
  obtain ⟨hinv, horb, hcc⟩ := h
  have hpow := PeriodicTM.TwoPointBridge.reflection_pow hinv hcc
  refine ⟨?_, ?_, ?_⟩
  · intro z
    show (f ^ k) (ι ((f ^ k) (ι z))) = z
    rw [hpow (ι z) k, hinv]
    have hgrp : f ^ k * f⁻¹ ^ k = 1 := by group
    calc (f ^ k) ((f⁻¹ ^ k) z) = (f ^ k * f⁻¹ ^ k) z := rfl
      _ = z := by rw [hgrp]; rfl
  · intro z
    exact (horb z).trans ⟨(k : ℤ), by rw [zpow_natCast]⟩
  · intro z
    show f ((f ^ k) (ι (f ((f ^ k) (ι z))))) = z
    have h1 : f ((f ^ k) (ι z)) = (f ^ (k + 1)) (ι z) := by
      rw [pow_succ']
      rfl
    rw [h1, hpow (ι z) (k + 1), hinv]
    have hgrp : f * (f ^ k * f⁻¹ ^ (k + 1)) = 1 := by group
    calc f ((f ^ k) ((f⁻¹ ^ (k + 1)) z))
        = (f * (f ^ k * f⁻¹ ^ (k + 1))) z := rfl
      _ = z := by rw [hgrp]; rfl

/-- **同一軌道の恒真対**: `0` と `1` が同じ軌道なら `(1, 0)` は良い出力。 -/
theorem goodOutput_one_zero {f : Perm (Fin N)} (hsc : f.SameCycle 0 1) :
    GoodOutput (0 : Fin N) 1 f 1 0 := by
  obtain ⟨hinv, horb, hcc⟩ := refl0_isReflection f
  obtain ⟨k, -, hk⟩ := ((horb 0).symm.trans hsc).exists_pow_eq'
  have hR := isReflection_pow_comp (ι := refl0 f) ⟨hinv, horb, hcc⟩ k
  refine ⟨fun z => (f ^ k) (refl0 f z), hR, hk, ?_⟩
  have hinv' := hR.1 0
  show (f ^ k) (refl0 f 1) = 0
  calc (f ^ k) (refl0 f 1)
      = (f ^ k) (refl0 f ((f ^ k) (refl0 f 0))) := by rw [hk]
    _ = 0 := hinv'

/-- 軌道ごとのシフト量（`0` の軌道は `k`、`1` の軌道は `j`、他は `0`）。 -/
private def shiftAmt (f : Perm (Fin N)) (k j : ℕ) (z : Fin N) : ℕ :=
  if f.SameCycle 0 z then k else if f.SameCycle 1 z then j else 0

/-- シフト量は軌道不変。 -/
private theorem shiftAmt_congr (f : Perm (Fin N)) (k j : ℕ) {w z : Fin N}
    (h : f.SameCycle w z) : shiftAmt f k j w = shiftAmt f k j z := by
  have e0 : f.SameCycle 0 w ↔ f.SameCycle 0 z :=
    ⟨fun a => a.trans h, fun a => a.trans h.symm⟩
  have e1 : f.SameCycle 1 w ↔ f.SameCycle 1 z :=
    ⟨fun a => a.trans h, fun a => a.trans h.symm⟩
  unfold shiftAmt
  by_cases h0 : f.SameCycle 0 w
  · rw [if_pos h0, if_pos (e0.mp h0)]
  · rw [if_neg h0]
    rw [if_neg (show ¬ f.SameCycle 0 z from fun hz => h0 (e0.mpr hz))]
    by_cases h1 : f.SameCycle 1 w
    · rw [if_pos h1, if_pos (e1.mp h1)]
    · rw [if_neg h1]
      rw [if_neg (show ¬ f.SameCycle 1 z from fun hz => h1 (e1.mpr hz))]

/-- **軌道ごとにずらした反射も反射**。 -/
theorem isReflection_orbit_shift {f : Perm (Fin N)} {ι : Fin N → Fin N}
    (h : IsReflection f ι) (k j : ℕ) :
    IsReflection f (fun z => (f ^ shiftAmt f k j z) (ι z)) := by
  obtain ⟨hinv, horb, hcc⟩ := h
  have hpow := PeriodicTM.TwoPointBridge.reflection_pow hinv hcc
  -- ι とシフトは軌道を保つので、shiftAmt は道中で変わらない
  have hshift_ι : ∀ z, shiftAmt f k j (ι z) = shiftAmt f k j z :=
    fun z => shiftAmt_congr f k j (horb z).symm
  have hshift_pow : ∀ (i : ℕ) (z : Fin N),
      shiftAmt f k j ((f ^ i) z) = shiftAmt f k j z :=
    fun i z => shiftAmt_congr f k j ⟨(i : ℤ), by rw [zpow_natCast]⟩ |>.symm
  have hshift_f : ∀ z, shiftAmt f k j (f z) = shiftAmt f k j z := by
    intro z
    have := hshift_pow 1 z
    simpa using this
  refine ⟨?_, ?_, ?_⟩
  · intro z
    set s := shiftAmt f k j z with hs
    have hs1 : shiftAmt f k j ((f ^ s) (ι z)) = s := by
      rw [hshift_pow, hshift_ι]
    show (f ^ shiftAmt f k j ((f ^ s) (ι z))) (ι ((f ^ s) (ι z))) = z
    rw [hs1, hpow (ι z) s, hinv]
    have hgrp : f ^ s * f⁻¹ ^ s = 1 := by group
    calc (f ^ s) ((f⁻¹ ^ s) z) = (f ^ s * f⁻¹ ^ s) z := rfl
      _ = z := by rw [hgrp]; rfl
  · intro z
    exact (horb z).trans
      ⟨(shiftAmt f k j z : ℤ), by rw [zpow_natCast]⟩
  · intro z
    set s := shiftAmt f k j z with hs
    have hsz : shiftAmt f k j ((f ^ s) (ι z)) = s := by
      rw [hshift_pow, hshift_ι]
    have hsz2 : shiftAmt f k j (f ((f ^ s) (ι z))) = s := by
      rw [hshift_f, hsz]
    show f ((f ^ shiftAmt f k j (f ((f ^ s) (ι z))))
      (ι (f ((f ^ s) (ι z))))) = z
    rw [hsz2]
    have h1 : f ((f ^ s) (ι z)) = (f ^ (s + 1)) (ι z) := by
      rw [pow_succ']
      rfl
    rw [h1, hpow (ι z) (s + 1), hinv]
    have hgrp : f * (f ^ s * f⁻¹ ^ (s + 1)) = 1 := by group
    calc f ((f ^ s) ((f⁻¹ ^ (s + 1)) z))
        = (f * (f ^ s * f⁻¹ ^ (s + 1))) z := rfl
      _ = z := by rw [hgrp]; rfl

/-- **別軌道の恒真族**: `0` と `1` が別軌道なら、`v₀ ∈ O(0)`・
`v₁ ∈ O(1)` の任意の対は良い出力。 -/
theorem goodOutput_cross {f : Perm (Fin N)} (hd : ¬ f.SameCycle 0 1)
    {v₀ v₁ : Fin N} (h₀ : f.SameCycle 0 v₀) (h₁ : f.SameCycle 1 v₁) :
    GoodOutput (0 : Fin N) 1 f v₀ v₁ := by
  obtain ⟨hinv, horb, hcc⟩ := refl0_isReflection f
  obtain ⟨k, -, hk⟩ := ((horb 0).symm.trans h₀).exists_pow_eq'
  obtain ⟨j, -, hj⟩ := ((horb 1).symm.trans h₁).exists_pow_eq'
  refine ⟨fun z => (f ^ shiftAmt f k j z) (refl0 f z),
    isReflection_orbit_shift ⟨hinv, horb, hcc⟩ k j, ?_, ?_⟩
  · show (f ^ shiftAmt f k j 0) (refl0 f 0) = v₀
    have hs0 : shiftAmt f k j 0 = k := by
      unfold shiftAmt
      rw [if_pos (Perm.SameCycle.refl f 0)]
    rw [hs0]
    exact hk
  · show (f ^ shiftAmt f k j 1) (refl0 f 1) = v₁
    have hs1 : shiftAmt f k j 1 = j := by
      unfold shiftAmt
      rw [if_neg hd, if_pos (Perm.SameCycle.refl f 1)]
    rw [hs1]
    exact hj

end

end PeriodicTM.Reflect

#print axioms PeriodicTM.Reflect.refl0_isReflection
#print axioms PeriodicTM.Reflect.goodOutput_one_zero
#print axioms PeriodicTM.Reflect.goodOutput_cross
