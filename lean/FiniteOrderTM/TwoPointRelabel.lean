/-
FiniteOrderTM/TwoPointRelabel.lean
— 付け替え（relabeling）の輸送と `extendPerm`（research/17 の修正方針 1）

グループ順の埋め込み（`AdvState.edges`）は存在証明のための1つの
標識付けにすぎない。付け替え `τ : Perm (Fin N)` に対し、`f` が辺集合を
拡張するなら `τ * f * τ⁻¹` は付け替えた辺集合を拡張し、約束
（`QueryGame.Valid`）・軌道関係（`SameCycle`）・出力の良さ
（`GoodOutput`）もすべて `τ` で輸送される（共役不変性）。

後半の `extendPerm` は「対応リスト `l₁ ↦ l₂`（各 Nodup・同長）を
実現する置換」の明示構成。木の帰納で、グループ順ラベルの列を
対局で実際に現れた頂点の列へ移す `τ` を葉で作るのに使う。

**BUILD NOTE**: root（`FiniteOrderTM.lean`）非取込。検査は
`lake env lean FiniteOrderTM/TwoPointRelabel.lean`。
-/
import FiniteOrderTM.QueryGame

namespace PeriodicTM.Relabel

open Equiv Finset

variable {N : ℕ}

/-! ### 共役の基本式 -/

/-- 共役の点ごとの作用。 -/
theorem conj_apply (τ f : Perm (Fin N)) (x : Fin N) :
    (τ * f * τ⁻¹) x = τ (f (τ⁻¹ x)) := rfl

/-- 共役と自然数冪の交換。 -/
theorem conj_pow (τ f : Perm (Fin N)) (n : ℕ) :
    (τ * f * τ⁻¹) ^ n = τ * f ^ n * τ⁻¹ := by
  have h := map_pow (MulAut.conj τ) f n
  simp only [MulAut.conj_apply] at h
  exact h.symm

/-- 共役と整数冪の交換。 -/
theorem conj_zpow (τ f : Perm (Fin N)) (n : ℤ) :
    (τ * f * τ⁻¹) ^ n = τ * f ^ n * τ⁻¹ := by
  have h := map_zpow (MulAut.conj τ) f n
  simp only [MulAut.conj_apply] at h
  exact h.symm

/-- **辺の輸送**: `f u = v` なら共役は付け替えた辺 `(τ u, τ v)` を拡張する。 -/
theorem conj_extends {τ f : Perm (Fin N)} {u v : Fin N} (h : f u = v) :
    (τ * f * τ⁻¹) (τ u) = τ v := by
  simp [conj_apply, h]

/-! ### 軌道関係と約束の輸送 -/

/-- `SameCycle` の共役不変性。 -/
theorem sameCycle_conj {τ f : Perm (Fin N)} {x y : Fin N} :
    (τ * f * τ⁻¹).SameCycle (τ x) (τ y) ↔ f.SameCycle x y := by
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, τ.injective ?_⟩
    rw [conj_zpow] at hi
    simpa [Perm.mul_apply] using hi
  · rintro ⟨i, hi⟩
    exact ⟨i, by simp [Perm.mul_apply, hi]⟩

/-- 軌道（`SameCycle` の解集合）は `τ` の像に移る。 -/
theorem orbit_conj (τ f : Perm (Fin N)) (x : Fin N) :
    ({y | (τ * f * τ⁻¹).SameCycle (τ x) y} : Finset (Fin N))
      = ({y | f.SameCycle x y} : Finset (Fin N)).image τ := by
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro hz
    refine ⟨τ⁻¹ z, ?_, by simp⟩
    have h : (τ * f * τ⁻¹).SameCycle (τ x) (τ (τ⁻¹ z)) := by simpa using hz
    exact sameCycle_conj.mp h
  · rintro ⟨w, hw, rfl⟩
    exact sameCycle_conj.mpr hw

/-- 軌道の大きさは共役で不変。 -/
theorem orbit_card_conj (τ f : Perm (Fin N)) (x : Fin N) :
    #{y | (τ * f * τ⁻¹).SameCycle (τ x) y} = #{y | f.SameCycle x y} := by
  rw [orbit_conj, Finset.card_image_of_injective _ τ.injective]

/-- **約束の輸送**: `τ` が指定点 `a` を固定すれば、`Valid` は共役で保たれる。 -/
theorem valid_conj {n ℓ : ℕ} {a : Fin N} {f : Perm (Fin N)} (τ : Perm (Fin N))
    (ha : τ a = a) (h : PeriodicTM.QueryGame.Valid n ℓ a f) :
    PeriodicTM.QueryGame.Valid n ℓ a (τ * f * τ⁻¹) := by
  obtain ⟨h1, h2⟩ := h
  constructor
  · rw [conj_pow, h1]
    group
  · rw [← ha, orbit_card_conj]
    exact h2

/-! ### GoodOutput の輸送 -/

/-- 反射の共役: `ι` が `f` の有効反射なら `τ ∘ ι ∘ τ⁻¹` は共役の有効反射。 -/
theorem isReflection_conj {f : Perm (Fin N)} {ι : Fin N → Fin N}
    (τ : Perm (Fin N)) (h : PeriodicTM.QueryGame.IsReflection f ι) :
    PeriodicTM.QueryGame.IsReflection (τ * f * τ⁻¹) (⇑τ ∘ ι ∘ ⇑τ⁻¹) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro x
    simp [Function.comp, h1]
  · intro x
    have h' := sameCycle_conj (τ := τ) (f := f)
      (x := τ⁻¹ x) (y := ι (τ⁻¹ x)) |>.mpr (h2 (τ⁻¹ x))
    simpa using h'
  · intro x
    simp [Perm.mul_apply, h3]

/-- `GoodOutput` の輸送（順方向）。 -/
theorem goodOutput_conj {f : Perm (Fin N)} {a b v₀ v₁ : Fin N}
    (τ : Perm (Fin N))
    (h : PeriodicTM.QueryGame.GoodOutput a b f v₀ v₁) :
    PeriodicTM.QueryGame.GoodOutput (τ a) (τ b) (τ * f * τ⁻¹) (τ v₀) (τ v₁) := by
  obtain ⟨ι, hrefl, ha, hb⟩ := h
  exact ⟨⇑τ ∘ ι ∘ ⇑τ⁻¹, isReflection_conj τ hrefl,
    by simp [Function.comp, ha], by simp [Function.comp, hb]⟩

/-- **`GoodOutput` の共役不変性**（両方向）。撃墜の輸送はこの ← 向きを使う:
共役側で良い出力なら元でも良い出力、対偶で「元で悪ければ共役でも悪い」。 -/
theorem goodOutput_conj_iff {f : Perm (Fin N)} {a b v₀ v₁ : Fin N}
    (τ : Perm (Fin N)) :
    PeriodicTM.QueryGame.GoodOutput (τ a) (τ b) (τ * f * τ⁻¹) (τ v₀) (τ v₁) ↔
      PeriodicTM.QueryGame.GoodOutput a b f v₀ v₁ := by
  constructor
  · intro h
    have h' := goodOutput_conj τ⁻¹ h
    have hgrp : τ⁻¹ * (τ * f * τ⁻¹) * τ = f := by group
    simpa [hgrp] using h'
  · exact goodOutput_conj τ

/-! ### `extendPerm` — 対応リストを実現する置換

`l₁`・`l₂` がともに Nodup で同じ長さのとき、`extendPerm l₁ l₂` は
各 `i` で `l₁[i] ↦ l₂[i]` を満たす置換。構成は先頭から順に
「まず残りを合わせ、先頭のずれを互換で直す」。リスト外の点での
値は指定しない（勝手な延長でよい）ことが使い所で、未開示点の
配置の自由度はここから出る。 -/

section ExtendPerm

variable {α : Type*} [DecidableEq α]

/-- 対応リスト `l₁ ↦ l₂` を実現する置換（`extendPerm_getElem`）。 -/
def extendPerm : List α → List α → Perm α
  | a :: l₁, b :: l₂ => Equiv.swap (extendPerm l₁ l₂ a) b * extendPerm l₁ l₂
  | _, _ => 1

/-- **`extendPerm` の指定どおりの作用**: `extendPerm l₁ l₂ l₁[i] = l₂[i]`。 -/
theorem extendPerm_getElem : ∀ (l₁ l₂ : List α), l₁.Nodup → l₂.Nodup →
    l₁.length = l₂.length → ∀ i, (hi : i < l₁.length) → (hi' : i < l₂.length) →
    extendPerm l₁ l₂ l₁[i] = l₂[i]
  | a :: l₁, b :: l₂, _, _, _, 0, _, _ => by
    simp only [extendPerm, List.getElem_cons_zero, Perm.mul_apply]
    exact Equiv.swap_apply_left _ _
  | a :: l₁, b :: l₂, hnd₁, hnd₂, hlen, i + 1, hi, hi' => by
    simp only [List.getElem_cons_succ, extendPerm, Perm.mul_apply]
    have ha := (List.nodup_cons.mp hnd₁).1
    have hb := (List.nodup_cons.mp hnd₂).1
    have hi₁ : i < l₁.length := by simpa using hi
    have hi₂ : i < l₂.length := by simpa using hi'
    have ih := extendPerm_getElem l₁ l₂ (List.nodup_cons.mp hnd₁).2
      (List.nodup_cons.mp hnd₂).2 (by simpa using hlen) i hi₁ hi₂
    rw [ih]
    refine Equiv.swap_apply_of_ne_of_ne ?_ ?_
    · intro heq
      have hgi : l₁[i] = a := (extendPerm l₁ l₂).injective (by rw [ih, heq])
      exact ha (hgi ▸ List.getElem_mem _)
    · intro heq
      exact hb (heq ▸ List.getElem_mem _)

/-- 写像版: `l₁` を `extendPerm l₁ l₂` で写すとちょうど `l₂`。 -/
theorem extendPerm_map (l₁ l₂ : List α) (h₁ : l₁.Nodup) (h₂ : l₂.Nodup)
    (hlen : l₁.length = l₂.length) :
    l₁.map (extendPerm l₁ l₂) = l₂ := by
  apply List.ext_getElem (by simpa using hlen)
  intro i hi hi'
  simp only [List.getElem_map]
  exact extendPerm_getElem l₁ l₂ h₁ h₂ hlen i (by simpa using hi) hi'

end ExtendPerm

end PeriodicTM.Relabel

#print axioms PeriodicTM.Relabel.goodOutput_conj_iff
#print axioms PeriodicTM.Relabel.valid_conj
#print axioms PeriodicTM.Relabel.conj_extends
#print axioms PeriodicTM.Relabel.sameCycle_conj
#print axioms PeriodicTM.Relabel.extendPerm_getElem
#print axioms PeriodicTM.Relabel.extendPerm_map
