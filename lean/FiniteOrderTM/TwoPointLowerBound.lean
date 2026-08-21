/-
FiniteOrderTM/TwoPointLowerBound.lean
— 定理9.6 の下界: `q < min (ℓ−2, k₁*)` の木は勝てない

research/18 の場合分け表の実装。部品:
* 対局と一致（`TwoPointConcrete`）: `playC` / `agreesC_of_extends` /
  `not_winsAt_of_bad_leafC`
* 葉での付け替え τ と完成の輸送（`TwoPointTransport`）
* 同一軌道 2 距離完成のデータ束（`TwoPointSameCycle` の
  `exists_sameCycleData`）
* 配置内訳つき別軌道完成（`TwoPointDiffCycle` の `exists_diffCycleData`）
* 型別撃墜（`TwoPointAdversary` の `type{1,2,4}_killed_two_distances`、
  `goodOutput_pos_relation`）

撃墜の割当（research/18）:
* v₁ が 0-側（Z）→ 別軌道完成（v₁ ∈ O(0) ⇒ v₁ ∉ O(1)）
* v₀ が 1-側（O1）→ 別軌道完成（v₀ ∈ O(1) ⇒ v₀ ∉ O(0)）
* 迷いB の成分 → 同一軌道完成で両軌道の外
* 残り（v₀ ∈ {Z, 迷いA, U} × v₁ ∈ {O', U}）→ 2 距離撃墜と資源
  （軌道外ラベル u ／共通尾部 w ／別軌道の配置自由度）

**BUILD NOTE**（2026-08-21 訂正）: 8bacb1d 以降 root
（`FiniteOrderTM.lean`）から取り込まれており、`lake build` の対象。
この注記の「非取込」は古い。
-/
import FiniteOrderTM.TwoPointTransport
import FiniteOrderTM.TwoPointSameCycle
import FiniteOrderTM.TwoPointDiffCycle

namespace PeriodicTM.ClaimA

open Equiv Finset
open PeriodicTM.QueryGame (Tree GoodOutput Runs Valid WinsAt)

variable {N : ℕ}

/-! ### 撃墜の小さな補題 -/

section Kills

variable [NeZero N]

/-- 共役と冪の作用。 -/
theorem conj_pow_apply (τ f : Perm (Fin N)) (n : ℕ) (x : Fin N) :
    ((τ * f * τ⁻¹) ^ n) (τ x) = τ ((f ^ n) x) := by
  rw [PeriodicTM.Relabel.conj_pow]
  simp [Perm.mul_apply]

/-- 第1成分が `0` の軌道外なら良い出力でない。 -/
theorem not_good_left {f : Perm (Fin N)} {v₀ v₁ : Fin N}
    (h : ¬ f.SameCycle 0 v₀) : ¬ GoodOutput (0 : Fin N) 1 f v₀ v₁ :=
  fun hg => h (goodOutput_sameCycle_left hg)

/-- 第2成分が `1` の軌道外なら良い出力でない。 -/
theorem not_good_right {f : Perm (Fin N)} {v₀ v₁ : Fin N}
    (h : ¬ f.SameCycle 1 v₁) : ¬ GoodOutput (0 : Fin N) 1 f v₀ v₁ :=
  fun hg => h (goodOutput_sameCycle_right hg)

/-- 別軌道完成では、`0` の軌道上の点を第2成分に出す対は死ぬ。 -/
theorem not_good_diff_right {f : Perm (Fin N)} {v₀ v₁ : Fin N}
    (hdiff : ¬ f.SameCycle 0 1) (hv₁ : f.SameCycle 0 v₁) :
    ¬ GoodOutput (0 : Fin N) 1 f v₀ v₁ :=
  not_good_right (fun h1 => hdiff (hv₁.trans h1.symm))

/-- 別軌道完成では、`1` の軌道上の点を第1成分に出す対は死ぬ。 -/
theorem not_good_diff_left {f : Perm (Fin N)} {v₀ v₁ : Fin N}
    (hdiff : ¬ f.SameCycle 0 1) (hv₀ : f.SameCycle 1 v₀) :
    ¬ GoodOutput (0 : Fin N) 1 f v₀ v₁ :=
  not_good_left (fun h0 => hdiff (h0.trans hv₀.symm))

/-- **定数不一致の撃墜**（型3形・単独完成）: `v₀` が位置 `d + α`、
`v₁` が定数位置 `β` で `α ≠ β`（ともに `< ℓ`）なら良い出力でない。 -/
theorem type3_const_killed {ℓ : ℕ} [NeZero N] (hℓ : 3 ≤ ℓ)
    {f : Perm (Fin N)}
    (hcard : #{y | f.SameCycle (0 : Fin N) y} = ℓ)
    {α β d : ℕ} {v₀ v₁ : Fin N}
    (hv₀ : v₀ = (f ^ (d + α)) (0 : Fin N))
    (hv₁ : v₁ = (f ^ β) (0 : Fin N))
    (hd : (1 : Fin N) = (f ^ d) (0 : Fin N))
    (hαβ : α ≠ β) (hα : α < ℓ) (hβ : β < ℓ) :
    ¬ GoodOutput (0 : Fin N) 1 f v₀ v₁ := by
  intro hg
  have hrel := goodOutput_pos_relation hcard hv₀ hv₁ hd hg
  have hz : (β : ZMod ℓ) = (α : ZMod ℓ) := by
    push_cast at hrel
    linear_combination hrel
  have := (ZMod.natCast_eq_natCast_iff _ _ _).mp hz
  have hmod := Nat.ModEq.eq_of_lt_of_lt this hβ hα
  omega

end Kills

/-! ### 葉の点の分類（τ ごと） -/

section Classify

variable [NeZero N]

/-- 使用点の粗い分類（τ に依らない）。 -/
theorem mem_used_cases (C : PathState N) (v : Fin N) :
    v ∉ C.used ∨ v ∈ (0 : Fin N) :: C.p0 ∨ v ∈ (1 : Fin N) :: C.p1 ∨
      ∃ p ∈ C.strays, v ∈ p.1 :: p.2 := by
  by_cases h : v ∈ C.used
  · right
    simp only [PathState.used, PathState.paths, List.flatten_cons,
      List.mem_append] at h
    rcases h with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · obtain ⟨l, hl, hvl⟩ := List.mem_flatten.mp h
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hl
      exact Or.inr (Or.inr ⟨p, hp, hvl⟩)
  · exact Or.inl h

/-- hseg の分節（0-パス・1-パス・ブロック）への分解。 -/
theorem hseg_parts {C : PathState N} {τ : Perm (Fin N)}
    (hseg : C.toAdv.gpaths.map (List.map (⇑τ ∘ Fin.ofNat N)) = C.paths) :
    ((List.range' 2 C.toAdv.k0).map (⇑τ ∘ Fin.ofNat N) = C.p0) ∧
    ((List.range' (2 + C.toAdv.k0) C.toAdv.k1).map (⇑τ ∘ Fin.ofNat N)
      = C.p1) ∧
    (C.toAdv.blocks.map (List.map (⇑τ ∘ Fin.ofNat N))
      = C.strays.map fun p => p.1 :: p.2) := by
  simp only [AdvState.gpaths, PathState.paths, List.map_cons,
    List.cons.injEq] at hseg
  exact ⟨hseg.1.2, hseg.2.1.2, hseg.2.2⟩

/-- **0-側の位置**: `v ∈ 0 :: p0` なら、ある `α ≤ k₀` があって、
どの完成の共役でも `v` は位置 `α`。 -/
theorem posZ_of_mem {C : PathState N} {τ : Perm (Fin N)}
    (hseg : C.toAdv.gpaths.map (List.map (⇑τ ∘ Fin.ofNat N)) = C.paths)
    (hτ0 : τ 0 = 0) {v : Fin N} (hv : v ∈ (0 : Fin N) :: C.p0) :
    ∃ α, α ≤ C.toAdv.k0 ∧ ∀ {ℓ : ℕ} (f₀ : Perm (Fin N)),
      IsCompletion N ℓ C.toAdv f₀ →
      ((τ * f₀ * τ⁻¹) ^ α) (0 : Fin N) = v := by
  have h0 : (0 : Fin N) = τ (Fin.ofNat N 0) := by
    rw [ofNat_zero_eq_zero, hτ0]
  rcases List.mem_cons.mp hv with rfl | hv'
  · exact ⟨0, Nat.zero_le _, fun f₀ _ => by simp⟩
  · rw [← (hseg_parts hseg).1] at hv'
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv'
    obtain ⟨h2x, hxk⟩ := List.mem_range'_1.mp hx
    refine ⟨(x - 2) + 1, by omega, fun f₀ hc => ?_⟩
    have hpos := completion_pow_zero C.toAdv f₀ hc (x - 2) (by omega)
    rw [show 2 + (x - 2) = x by omega] at hpos
    rw [h0, conj_pow_apply, hpos]
    rfl

/-- **1-側の位置**: `v ∈ 1 :: p1` なら、ある `a ≤ k₁` があって、
距離 `d` を実現するどの完成の共役でも `v` は位置 `d + a`。 -/
theorem posO_of_mem {C : PathState N} {τ : Perm (Fin N)}
    (hseg : C.toAdv.gpaths.map (List.map (⇑τ ∘ Fin.ofNat N)) = C.paths)
    (hτ0 : τ 0 = 0) (hτ1 : τ 1 = 1) (hN2 : 2 ≤ N)
    {v : Fin N} (hv : v ∈ (1 : Fin N) :: C.p1) :
    ∃ a, a ≤ C.toAdv.k1 ∧ ∀ {ℓ : ℕ} (f₀ : Perm (Fin N)) (d : ℕ),
      IsCompletion N ℓ C.toAdv f₀ →
      (1 : Fin N) = (f₀ ^ d) (0 : Fin N) →
      ((τ * f₀ * τ⁻¹) ^ (d + a)) (0 : Fin N) = v := by
  have h0 : (0 : Fin N) = τ (Fin.ofNat N 0) := by
    rw [ofNat_zero_eq_zero, hτ0]
  have h1 : (1 : Fin N) = τ (Fin.ofNat N 1) := by
    rw [ofNat_one_eq_one hN2, hτ1]
  rcases List.mem_cons.mp hv with rfl | hv'
  · refine ⟨0, Nat.zero_le _, fun f₀ d hc hd => ?_⟩
    rw [Nat.add_zero, h0, conj_pow_apply]
    have hd' : (f₀ ^ d) (Fin.ofNat N 0) = Fin.ofNat N 1 := by
      rw [ofNat_zero_eq_zero, ← hd, ofNat_one_eq_one hN2]
    rw [hd', ← h1]
  · rw [← (hseg_parts hseg).2.1] at hv'
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv'
    obtain ⟨h2x, hxk⟩ := List.mem_range'_1.mp hx
    refine ⟨(x - 2 - C.toAdv.k0) + 1, by omega, fun f₀ d hc hd => ?_⟩
    have hd' : Fin.ofNat N 1 = (f₀ ^ d) (Fin.ofNat N 0) := by
      rw [ofNat_zero_eq_zero, ofNat_one_eq_one hN2]
      exact hd
    have hpos := completion_onP1_pos C.toAdv f₀ hc hd'
      (x - 2 - C.toAdv.k0) (by omega)
    rw [show 2 + C.toAdv.k0 + (x - 2 - C.toAdv.k0) = x by omega] at hpos
    rw [h0, conj_pow_apply]
    rw [show d + ((x - 2 - C.toAdv.k0) + 1)
      = ((x - 2 - C.toAdv.k0) + 1) + d by omega, hpos]
    rfl

/-- **迷い点の分類**: 迷いパス上の点は、あるブロックのラベルの像。 -/
theorem stray_of_mem {C : PathState N} {τ : Perm (Fin N)}
    (hseg : C.toAdv.gpaths.map (List.map (⇑τ ∘ Fin.ofNat N)) = C.paths)
    {v : Fin N} (hv : ∃ p ∈ C.strays, v ∈ p.1 :: p.2) :
    ∃ b ∈ C.toAdv.blocks, ∃ x ∈ b, τ (Fin.ofNat N x) = v := by
  obtain ⟨p, hp, hvp⟩ := hv
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hp
  have hseg2 := (hseg_parts hseg).2.2
  have hlen : C.toAdv.blocks.length = C.strays.length := by
    have := congrArg List.length hseg2
    simpa using this
  have hkey := congrArg (fun l => l[k]?) hseg2
  simp only [List.getElem?_map] at hkey
  rw [List.getElem?_eq_getElem (by omega : k < C.toAdv.blocks.length),
    List.getElem?_eq_getElem hk] at hkey
  simp only [Option.map_some] at hkey
  have hbk : (C.toAdv.blocks[k]'(by omega)).map (⇑τ ∘ Fin.ofNat N)
      = C.strays[k].1 :: C.strays[k].2 := by
    exact Option.some.inj hkey
  rw [← hbk] at hvp
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hvp
  exact ⟨_, List.getElem_mem _, x, hx, rfl⟩

end Classify

/-! ### 共役の運搬（枝で繰り返し使う形） -/

section Conj

variable [NeZero N]

/-- 距離の共役。 -/
theorem conj_dist {τ f : Perm (Fin N)} {d : ℕ} (hτ0 : τ 0 = 0)
    (hτ1 : τ 1 = 1) (h : (1 : Fin N) = (f ^ d) 0) :
    (1 : Fin N) = ((τ * f * τ⁻¹) ^ d) 0 := by
  have hc := conj_pow_apply τ f d 0
  rw [hτ0] at hc
  rw [hc, ← h, hτ1]

/-- 位置の共役。 -/
theorem conj_pos {τ f : Perm (Fin N)} {α : ℕ} {w v : Fin N} (hτ0 : τ 0 = 0)
    (h : (f ^ α) 0 = w) (hw : τ w = v) :
    ((τ * f * τ⁻¹) ^ α) 0 = v := by
  have hc := conj_pow_apply τ f α 0
  rw [hτ0] at hc
  rw [hc, h, hw]

/-- 非同一軌道の共役。 -/
theorem conj_not_sc {τ f : Perm (Fin N)} {a b a' b' : Fin N}
    (ha : τ a = a') (hb : τ b = b') (h : ¬ f.SameCycle a b) :
    ¬ (τ * f * τ⁻¹).SameCycle a' b' := by
  intro hc
  apply h
  have hiff := PeriodicTM.Relabel.sameCycle_conj (τ := τ) (f := f)
    (x := a) (y := b)
  rw [ha, hb] at hiff
  exact hiff.mp hc

/-- 同一軌道の共役。 -/
theorem conj_sc {τ f : Perm (Fin N)} {a b a' b' : Fin N}
    (ha : τ a = a') (hb : τ b = b') (h : f.SameCycle a b) :
    (τ * f * τ⁻¹).SameCycle a' b' := by
  have hiff := PeriodicTM.Relabel.sameCycle_conj (τ := τ) (f := f)
    (x := a) (y := b)
  rw [ha, hb] at hiff
  exact hiff.mpr h

/-- 0-側の点は任意の完成で `0` と同一軌道（f₀ 側）。 -/
theorem sameCycle_zero_of_label {ℓ : ℕ} {s : AdvState} {f₀ : Perm (Fin N)}
    (hc : IsCompletion N ℓ s f₀) {x : ℕ}
    (hx : x ∈ (0 : ℕ) :: List.range' 2 s.k0) :
    f₀.SameCycle (Fin.ofNat N 0) (Fin.ofNat N x) := by
  rcases List.mem_cons.mp hx with rfl | hx'
  · exact Perm.SameCycle.refl _ _
  · obtain ⟨h2x, hxk⟩ := List.mem_range'_1.mp hx'
    refine ⟨((x - 2) + 1 : ℕ), ?_⟩
    rw [zpow_natCast]
    have := completion_pow_zero s f₀ hc (x - 2) (by omega)
    rw [this]
    congr 1
    omega

/-- 1-側の点は任意の完成で `1` と同一軌道（f₀ 側）。 -/
theorem sameCycle_one_of_label {ℓ : ℕ} {s : AdvState} {f₀ : Perm (Fin N)}
    (hc : IsCompletion N ℓ s f₀) (hN2 : 2 ≤ N) {x : ℕ}
    (hx : x ∈ (1 : ℕ) :: List.range' (2 + s.k0) s.k1) :
    f₀.SameCycle (Fin.ofNat N 1) (Fin.ofNat N x) := by
  rcases List.mem_cons.mp hx with rfl | hx'
  · exact Perm.SameCycle.refl _ _
  · obtain ⟨h2x, hxk⟩ := List.mem_range'_1.mp hx'
    refine ⟨((x - 2 - s.k0) + 1 : ℕ), ?_⟩
    rw [zpow_natCast]
    have := completion_pow_one s f₀ hc (x - 2 - s.k0) (by omega)
    rw [this]
    congr 1
    omega

/-- 0-側の会員は共役完成で `0` と同一軌道（conc 側）。 -/
theorem sc_zero_of_mem {C : PathState N} {τ : Perm (Fin N)}
    (hseg : C.toAdv.gpaths.map (List.map (⇑τ ∘ Fin.ofNat N)) = C.paths)
    (hτ0 : τ 0 = 0) {v : Fin N} (hv : v ∈ (0 : Fin N) :: C.p0)
    {ℓ : ℕ} (f₀ : Perm (Fin N)) (hc : IsCompletion N ℓ C.toAdv f₀) :
    (τ * f₀ * τ⁻¹).SameCycle 0 v := by
  have h0 : τ (Fin.ofNat N 0) = 0 := by rw [ofNat_zero_eq_zero, hτ0]
  rcases List.mem_cons.mp hv with rfl | hv'
  · exact Perm.SameCycle.refl _ _
  · rw [← (hseg_parts hseg).1] at hv'
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv'
    exact conj_sc h0 rfl (sameCycle_zero_of_label hc
      (List.mem_cons.mpr (Or.inr hx)))

/-- 1-側の会員は共役完成で `1` と同一軌道（conc 側）。 -/
theorem sc_one_of_mem {C : PathState N} {τ : Perm (Fin N)}
    (hseg : C.toAdv.gpaths.map (List.map (⇑τ ∘ Fin.ofNat N)) = C.paths)
    (hτ1 : τ 1 = 1) (hN2 : 2 ≤ N) {v : Fin N}
    (hv : v ∈ (1 : Fin N) :: C.p1)
    {ℓ : ℕ} (f₀ : Perm (Fin N)) (hc : IsCompletion N ℓ C.toAdv f₀) :
    (τ * f₀ * τ⁻¹).SameCycle 1 v := by
  have h1 : τ (Fin.ofNat N 1) = 1 := by rw [ofNat_one_eq_one hN2, hτ1]
  rcases List.mem_cons.mp hv with rfl | hv'
  · exact Perm.SameCycle.refl _ _
  · rw [← (hseg_parts hseg).2.1] at hv'
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv'
    exact conj_sc h1 rfl (sameCycle_one_of_label hc hN2
      (List.mem_cons.mpr (Or.inr hx)))

end Conj

/-! ### 主定理: 下界 -/

section Main

variable [NeZero N]

/-- **定理 9.6（下界）**: `q < min (ℓ − 2, k₁*(N, ℓ))` のとき、
深さ `q` のどの適応的決定木も 2 点整合ゲームに勝てない。 -/
theorem two_point_lower_bound {ℓ q : ℕ} (hℓ : 3 ≤ ℓ)
    (hq : q < min (ℓ - 2) (PeriodicTM.TwoPointCore.k1Star N ℓ)) :
    ¬ ∃ t : Tree N q, WinsAt ℓ ℓ (0 : Fin N) 1 t := by
  rintro ⟨t, hwin⟩
  -- 領域の数値
  have hqk : q < PeriodicTM.TwoPointCore.k1Star N ℓ :=
    lt_of_lt_of_le hq (min_le_right _ _)
  have hq2 : q < ℓ - 2 := lt_of_lt_of_le hq (min_le_left _ _)
  have hnk := PeriodicTM.TwoPointCore.not_kills_of_lt_k1Star hqk
  unfold PeriodicTM.TwoPointCore.Kills at hnk
  push_neg at hnk
  obtain ⟨m, hmℓ, hmq, hmdvd, hmN⟩ := hnk
  have hN2 : 2 ≤ N := by omega
  -- 対局
  obtain ⟨hInv, hlen⟩ := playC_inv t (PathState.init N) (init_inv hN2)
    (by rw [init_used_length]; omega)
  rw [init_used_length] at hlen
  set C : PathState N := playC t (PathState.init N) with hC
  set s := C.toAdv with hs
  have hsq : s.q ≤ q := by
    have h := playC_toAdv_q t (PathState.init N)
    rw [← hC] at h
    rw [hs]
    have h0 : (PathState.init N).toAdv.q = 0 := rfl
    omega
  have hfit : s.Fits N := by
    constructor
    · intro j hj
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hj
      have hne := hInv.2 p hp
      cases hpp : p.2 with
      | nil => exact absurd hpp hne
      | cons a l => simp [hpp]
    · show C.toAdv.vertexCount ≤ N
      rw [← used_length]
      have := hInv.1.length_le_card
      simpa using this
  have hreg : InLowerRegion N ℓ s := lt_of_le_of_lt hsq hq
  have hrs : s.strays.length ≤ s.strays.sum := length_le_sum hfit.1
  have hsqdef : s.q = s.k0 + s.k1 + s.strays.sum := rfl
  have hvc : s.vertexCount
      = 2 + s.k0 + s.k1 + s.strays.sum + s.strays.length := rfl
  have hvcN : s.vertexCount < N := by omega
  -- データ束
  obtain ⟨D⟩ := exists_sameCycleData s hfit hreg hℓ
  obtain ⟨E⟩ := exists_diffCycleData s hfit hreg hℓ
  -- 葉の出力
  set v₀ := (playLeafC t (PathState.init N)).1 with hv₀
  set v₁ := (playLeafC t (PathState.init N)).2 with hv₁
  -- 撃墜スキーム: ext つきの τ と、任意の完成の共役の良い出力
  have master : ∀ (ext₁ : List ℕ) (ext₂ : List (Fin N)),
      (∀ u ∈ ext₁, s.vertexCount ≤ u) → (∀ u ∈ ext₁, u < N) →
      ext₁.Nodup → (∀ w ∈ ext₂, w ∉ C.used) → ext₂.Nodup →
      ext₁.length = ext₂.length →
      ∃ τ : Perm (Fin N), τ 0 = 0 ∧ τ 1 = 1 ∧
        (C.toAdv.gpaths.map (List.map (⇑τ ∘ Fin.ofNat N)) = C.paths) ∧
        (∀ p ∈ ext₁.zip ext₂, τ (Fin.ofNat N p.1) = p.2) ∧
        ∀ f₀ : Perm (Fin N), IsCompletion N ℓ s f₀ →
          #{y | (τ * f₀ * τ⁻¹).SameCycle (0 : Fin N) y} = ℓ ∧
          GoodOutput (0 : Fin N) 1 (τ * f₀ * τ⁻¹) v₀ v₁ := by
    intro ext₁ ext₂ hlo hltN hnd₁ hfr hnd₂ hlen'
    obtain ⟨τ, hτ0, hτ1, hseg, hext⟩ := exists_leaf_transport C hInv hN2
      ext₁ ext₂ hltN
      (fun u hu hmem => by
        have h1 := gpaths_flatten_lt C.toAdv (le_refl _) u hmem
        have h2 := hlo u hu
        rw [hs] at h2
        omega)
      hnd₁ hfr hnd₂ hlen'
    refine ⟨τ, hτ0, hτ1, hseg, hext, fun f₀ hc => ?_⟩
    obtain ⟨hval, hedges⟩ := transport_completion C hτ0 hseg hc
    have hagree := agreesC_of_extends (τ * f₀ * τ⁻¹) t (PathState.init N)
      (by rw [← hC]; exact hedges)
    have hgood := (runsC_iff_goodOutput 0 1 _ t (PathState.init N)
      hagree).mp (hwin _ hval)
    exact ⟨hval.2, hgood⟩
  -- 分類して撃墜する
  rcases mem_used_cases C v₀ with hU₀ | hZ₀ | hO₀ | hS₀
  · -- v₀ が未開示
    rcases mem_used_cases C v₁ with hU₁ | hZ₁ | hO₁ | hS₁
    · -- (U, U): 別軌道完成の配置自由度
      rcases E.hres with ⟨u, huvc, huN, -, hu0⟩ | hres
      · obtain ⟨τ, hτ0, hτ1, hseg, hext, hall⟩ := master [u] [v₀]
          (by simpa using huvc) (by simpa using huN) (by simp)
          (by simpa using hU₀) (by simp) rfl
        obtain ⟨-, hgood⟩ := hall E.f E.comp
        exact not_good_left (conj_not_sc hτ0
          (hext (u, v₀) (by simp)) hu0) hgood
      · obtain ⟨τ, hτ0, hτ1, hseg, hext, hall⟩ := master
          [s.vertexCount] [v₁]
          (by simp) (by simpa using hvcN) (by simp)
          (by simpa using hU₁) (by simp) rfl
        obtain ⟨-, hgood⟩ := hall E.f E.comp
        exact not_good_right (conj_not_sc hτ1
          (hext (s.vertexCount, v₁) (by simp))
          (hres s.vertexCount (le_refl _) hvcN)) hgood
    · -- (U, Z): 別軌道で v₁ ∈ O(0)
      obtain ⟨τ, hτ0, hτ1, hseg, -, hall⟩ := master [] [] (by simp)
        (by simp) (by simp) (by simp) (by simp) rfl
      obtain ⟨-, hgood⟩ := hall E.f E.comp
      have hdiffF := conj_not_sc hτ0 hτ1 E.hdiff
      exact not_good_diff_right hdiffF
        (sc_zero_of_mem hseg hτ0 hZ₁ E.f E.comp) hgood
    · -- (U, O1): 資源で v₀ を固定
      rcases D.resource with ⟨u, huvc, huN, hu₀, hu₁⟩ | ⟨w, hwvc, hwN, hw₀, hw₁⟩
      · -- 軌道外: v₀ ∉ O(0)
        obtain ⟨τ, hτ0, hτ1, hseg, hext, hall⟩ := master [u] [v₀]
          (by simpa using huvc) (by simpa using huN) (by simp)
          (by simpa using hU₀) (by simp) rfl
        obtain ⟨-, hgood⟩ := hall D.f₀ D.comp₀
        exact not_good_left (conj_not_sc hτ0
          (hext (u, v₀) (by simp)) hu₀.1) hgood
      · -- 共通尾部: v₀ の位置は両完成で ℓ−1、型2 で撃墜
        obtain ⟨τ, hτ0, hτ1, hseg, hext, hall⟩ := master [w] [v₀]
          (by simpa using hwvc) (by simpa using hwN) (by simp)
          (by simpa using hU₀) (by simp) rfl
        obtain ⟨hcard₀, hgood₀⟩ := hall D.f₀ D.comp₀
        obtain ⟨hcard₁, hgood₁⟩ := hall D.f₁ D.comp₁
        obtain ⟨b, hb, hposO⟩ := posO_of_mem hseg hτ0 hτ1 hN2 hO₁
        exact type2_killed_two_distances hℓ hcard₀ hcard₁
          (conj_pos hτ0 hw₀ (hext (w, v₀) (by simp))).symm
          (conj_pos hτ0 hw₁ (hext (w, v₀) (by simp))).symm
          (hposO D.f₀ D.d D.comp₀ D.dist₀).symm
          (hposO D.f₁ (D.d + 1) D.comp₁ D.dist₁).symm
          (conj_dist hτ0 hτ1 D.dist₀) (conj_dist hτ0 hτ1 D.dist₁)
          hgood₀ hgood₁
    · -- (U, 迷い)
      obtain ⟨τ, hτ0, hτ1, hseg, -, hall⟩ := master [] [] (by simp)
        (by simp) (by simp) (by simp) (by simp) rfl
      obtain ⟨bl, hbl, x, hx, hτx⟩ := stray_of_mem hseg hS₁
      rcases D.cover bl hbl with hbA | hbB
      · -- 迷いA: 位置 d + (1 + k₁ + j)。資源で場合分けし直す
        have hxA : x ∈ D.bA.flatten := List.mem_flatten.mpr ⟨bl, hbA, hx⟩
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hxA
        rcases D.resource with ⟨u, huvc, huN, hu₀, hu₁⟩ |
          ⟨w, hwvc, hwN, hw₀, hw₁⟩
        · obtain ⟨τ', hτ0', hτ1', hseg', hext', hall'⟩ := master [u] [v₀]
            (by simpa using huvc) (by simpa using huN) (by simp)
            (by simpa using hU₀) (by simp) rfl
          obtain ⟨-, hgood⟩ := hall' D.f₀ D.comp₀
          exact not_good_left (conj_not_sc hτ0'
            (hext' (u, v₀) (by simp)) hu₀.1) hgood
        · obtain ⟨τ', hτ0', hτ1', hseg', hext', hall'⟩ := master [w] [v₀]
            (by simpa using hwvc) (by simpa using hwN) (by simp)
            (by simpa using hU₀) (by simp) rfl
          obtain ⟨hcard₀, hgood₀⟩ := hall' D.f₀ D.comp₀
          obtain ⟨hcard₁, hgood₁⟩ := hall' D.f₁ D.comp₁
          obtain ⟨bl', hbl', x', hx', hτx'⟩ := stray_of_mem hseg' hS₁
          rcases D.cover bl' hbl' with hbA' | hbB'
          · have hxA' : x' ∈ D.bA.flatten :=
              List.mem_flatten.mpr ⟨bl', hbA', hx'⟩
            obtain ⟨j', hj', rfl⟩ := List.getElem_of_mem hxA'
            exact type2_killed_two_distances hℓ hcard₀ hcard₁
              (conj_pos hτ0' hw₀ (hext' (w, v₀) (by simp))).symm
              (conj_pos hτ0' hw₁ (hext' (w, v₀) (by simp))).symm
              (conj_pos hτ0' (D.strayA₀ j' hj') hτx').symm
              (conj_pos hτ0' (D.strayA₁ j' hj') hτx').symm
              (conj_dist hτ0' hτ1' D.dist₀) (conj_dist hτ0' hτ1' D.dist₁)
              hgood₀ hgood₁
          · have hxB' : x' ∈ D.bB.flatten :=
              List.mem_flatten.mpr ⟨bl', hbB', hx'⟩
            exact not_good_right (conj_not_sc hτ1' hτx'
              (D.offB₀ x' hxB').2) hgood₀
      · -- 迷いB: v₁ は両軌道の外
        obtain ⟨-, hgood⟩ := hall D.f₀ D.comp₀
        have hxB : x ∈ D.bB.flatten := List.mem_flatten.mpr ⟨bl, hbB, hx⟩
        exact not_good_right (conj_not_sc hτ1 hτx
          (D.offB₀ x hxB).2) hgood
  · -- v₀ が 0-側
    obtain ⟨τ, hτ0, hτ1, hseg, -, hall⟩ := master [] [] (by simp)
      (by simp) (by simp) (by simp) (by simp) rfl
    obtain ⟨α, hα, hposZ⟩ := posZ_of_mem hseg hτ0 hZ₀
    rcases mem_used_cases C v₁ with hU₁ | hZ₁ | hO₁ | hS₁
    · -- (Z, U): 資源
      rcases D.resource with ⟨u, huvc, huN, hu₀, hu₁⟩ |
        ⟨w, hwvc, hwN, hw₀, hw₁⟩
      · obtain ⟨τ', hτ0', hτ1', hseg', hext', hall'⟩ := master [u] [v₁]
          (by simpa using huvc) (by simpa using huN) (by simp)
          (by simpa using hU₁) (by simp) rfl
        obtain ⟨-, hgood⟩ := hall' D.f₀ D.comp₀
        exact not_good_right (conj_not_sc hτ1'
          (hext' (u, v₁) (by simp)) hu₀.2) hgood
      · obtain ⟨τ', hτ0', hτ1', hseg', hext', hall'⟩ := master [w] [v₁]
          (by simpa using hwvc) (by simpa using hwN) (by simp)
          (by simpa using hU₁) (by simp) rfl
        obtain ⟨hcard₀, hgood₀⟩ := hall' D.f₀ D.comp₀
        obtain ⟨hcard₁, hgood₁⟩ := hall' D.f₁ D.comp₁
        obtain ⟨α', hα', hposZ'⟩ := posZ_of_mem hseg' hτ0' hZ₀
        exact type1_killed_two_distances hℓ hcard₀ hcard₁
          (hposZ' D.f₀ D.comp₀).symm
          (conj_pos hτ0' hw₀ (hext' (w, v₁) (by simp))).symm
          (hposZ' D.f₁ D.comp₁).symm
          (conj_pos hτ0' hw₁ (hext' (w, v₁) (by simp))).symm
          (conj_dist hτ0' hτ1' D.dist₀) (conj_dist hτ0' hτ1' D.dist₁)
          hgood₀ hgood₁
    · -- (Z, Z): 別軌道
      obtain ⟨-, hgood⟩ := hall E.f E.comp
      exact not_good_diff_right (conj_not_sc hτ0 hτ1 E.hdiff)
        (sc_zero_of_mem hseg hτ0 hZ₁ E.f E.comp) hgood
    · -- (Z, O1): 型2
      obtain ⟨hcard₀, hgood₀⟩ := hall D.f₀ D.comp₀
      obtain ⟨hcard₁, hgood₁⟩ := hall D.f₁ D.comp₁
      obtain ⟨b, hb, hposO⟩ := posO_of_mem hseg hτ0 hτ1 hN2 hO₁
      exact type2_killed_two_distances hℓ hcard₀ hcard₁
        (hposZ D.f₀ D.comp₀).symm (hposZ D.f₁ D.comp₁).symm
        (hposO D.f₀ D.d D.comp₀ D.dist₀).symm
        (hposO D.f₁ (D.d + 1) D.comp₁ D.dist₁).symm
        (conj_dist hτ0 hτ1 D.dist₀) (conj_dist hτ0 hτ1 D.dist₁)
        hgood₀ hgood₁
    · -- (Z, 迷い)
      obtain ⟨bl, hbl, x, hx, hτx⟩ := stray_of_mem hseg hS₁
      rcases D.cover bl hbl with hbA | hbB
      · have hxA : x ∈ D.bA.flatten := List.mem_flatten.mpr ⟨bl, hbA, hx⟩
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hxA
        obtain ⟨hcard₀, hgood₀⟩ := hall D.f₀ D.comp₀
        obtain ⟨hcard₁, hgood₁⟩ := hall D.f₁ D.comp₁
        exact type2_killed_two_distances hℓ hcard₀ hcard₁
          (hposZ D.f₀ D.comp₀).symm (hposZ D.f₁ D.comp₁).symm
          (conj_pos hτ0 (D.strayA₀ j hj) hτx).symm
          (conj_pos hτ0 (D.strayA₁ j hj) hτx).symm
          (conj_dist hτ0 hτ1 D.dist₀) (conj_dist hτ0 hτ1 D.dist₁)
          hgood₀ hgood₁
      · obtain ⟨-, hgood⟩ := hall D.f₀ D.comp₀
        have hxB : x ∈ D.bB.flatten := List.mem_flatten.mpr ⟨bl, hbB, hx⟩
        exact not_good_right (conj_not_sc hτ1 hτx
          (D.offB₀ x hxB).2) hgood
  · -- v₀ が 1-側: 別軌道
    obtain ⟨τ, hτ0, hτ1, hseg, -, hall⟩ := master [] [] (by simp)
      (by simp) (by simp) (by simp) (by simp) rfl
    obtain ⟨-, hgood⟩ := hall E.f E.comp
    exact not_good_diff_left (conj_not_sc hτ0 hτ1 E.hdiff)
      (sc_one_of_mem hseg hτ1 hN2 hO₀ E.f E.comp) hgood
  · -- v₀ が迷い
    obtain ⟨τ, hτ0, hτ1, hseg, -, hall⟩ := master [] [] (by simp)
      (by simp) (by simp) (by simp) (by simp) rfl
    obtain ⟨bl, hbl, x, hx, hτx⟩ := stray_of_mem hseg hS₀
    rcases D.cover bl hbl with hbA | hbB
    · -- 迷いA: 位置 d + (1 + k₁ + j₀)
      have hxA : x ∈ D.bA.flatten := List.mem_flatten.mpr ⟨bl, hbA, hx⟩
      obtain ⟨j₀, hj₀, rfl⟩ := List.getElem_of_mem hxA
      rcases mem_used_cases C v₁ with hU₁ | hZ₁ | hO₁ | hS₁
      · -- (SA, U): 資源
        rcases D.resource with ⟨u, huvc, huN, hu₀, hu₁⟩ |
          ⟨w, hwvc, hwN, hw₀, hw₁⟩
        · obtain ⟨τ', hτ0', hτ1', hseg', hext', hall'⟩ := master [u] [v₁]
            (by simpa using huvc) (by simpa using huN) (by simp)
            (by simpa using hU₁) (by simp) rfl
          obtain ⟨-, hgood⟩ := hall' D.f₀ D.comp₀
          exact not_good_right (conj_not_sc hτ1'
            (hext' (u, v₁) (by simp)) hu₀.2) hgood
        · -- 型3形の定数不一致（単独完成）
          obtain ⟨τ', hτ0', hτ1', hseg', hext', hall'⟩ := master [w] [v₁]
            (by simpa using hwvc) (by simpa using hwN) (by simp)
            (by simpa using hU₁) (by simp) rfl
          obtain ⟨hcard₀, hgood₀⟩ := hall' D.f₀ D.comp₀
          obtain ⟨bl', hbl', x', hx', hτx'⟩ := stray_of_mem hseg' hS₀
          rcases D.cover bl' hbl' with hbA' | hbB'
          · have hxA' : x' ∈ D.bA.flatten :=
              List.mem_flatten.mpr ⟨bl', hbA', hx'⟩
            obtain ⟨j', hj', rfl⟩ := List.getElem_of_mem hxA'
            have hSumA := D.hSumA
            exact type3_const_killed hℓ hcard₀
              (conj_pos hτ0' (D.strayA₀ j' hj') hτx').symm
              (conj_pos hτ0' hw₀ (hext' (w, v₁) (by simp))).symm
              (conj_dist hτ0' hτ1' D.dist₀)
              (by omega) (by omega) (by omega) hgood₀
          · exact not_good_left (conj_not_sc hτ0' hτx'
              (D.offB₀ x' (List.mem_flatten.mpr ⟨bl', hbB', hx'⟩)).1) hgood₀
      · -- (SA, Z): 別軌道で v₁ ∈ O(0)
        obtain ⟨-, hgood⟩ := hall E.f E.comp
        exact not_good_diff_right (conj_not_sc hτ0 hτ1 E.hdiff)
          (sc_zero_of_mem hseg hτ0 hZ₁ E.f E.comp) hgood
      · -- (SA, O1): 型4
        obtain ⟨hcard₀, hgood₀⟩ := hall D.f₀ D.comp₀
        obtain ⟨hcard₁, hgood₁⟩ := hall D.f₁ D.comp₁
        obtain ⟨b, hb, hposO⟩ := posO_of_mem hseg hτ0 hτ1 hN2 hO₁
        exact type4_killed_two_distances hℓ hcard₀ hcard₁
          (conj_pos hτ0 (D.strayA₀ j₀ hj₀) hτx).symm
          (conj_pos hτ0 (D.strayA₁ j₀ hj₀) hτx).symm
          (hposO D.f₀ D.d D.comp₀ D.dist₀).symm
          (hposO D.f₁ (D.d + 1) D.comp₁ D.dist₁).symm
          (conj_dist hτ0 hτ1 D.dist₀) (conj_dist hτ0 hτ1 D.dist₁)
          hgood₀ hgood₁
      · -- (SA, 迷い)
        obtain ⟨bl', hbl', x', hx', hτx'⟩ := stray_of_mem hseg hS₁
        rcases D.cover bl' hbl' with hbA' | hbB'
        · have hxA' : x' ∈ D.bA.flatten :=
            List.mem_flatten.mpr ⟨bl', hbA', hx'⟩
          obtain ⟨j₁, hj₁, rfl⟩ := List.getElem_of_mem hxA'
          obtain ⟨hcard₀, hgood₀⟩ := hall D.f₀ D.comp₀
          obtain ⟨hcard₁, hgood₁⟩ := hall D.f₁ D.comp₁
          exact type4_killed_two_distances hℓ hcard₀ hcard₁
            (conj_pos hτ0 (D.strayA₀ j₀ hj₀) hτx).symm
            (conj_pos hτ0 (D.strayA₁ j₀ hj₀) hτx).symm
            (conj_pos hτ0 (D.strayA₀ j₁ hj₁) hτx').symm
            (conj_pos hτ0 (D.strayA₁ j₁ hj₁) hτx').symm
            (conj_dist hτ0 hτ1 D.dist₀) (conj_dist hτ0 hτ1 D.dist₁)
            hgood₀ hgood₁
        · obtain ⟨-, hgood⟩ := hall D.f₀ D.comp₀
          exact not_good_right (conj_not_sc hτ1 hτx'
            (D.offB₀ x' (List.mem_flatten.mpr ⟨bl', hbB', hx'⟩)).2) hgood
    · -- 迷いB: v₀ は 0 の軌道の外
      obtain ⟨-, hgood⟩ := hall D.f₀ D.comp₀
      have hxB : x ∈ D.bB.flatten := List.mem_flatten.mpr ⟨bl, hbB, hx⟩
      exact not_good_left (conj_not_sc hτ0 hτx
        (D.offB₀ x hxB).1) hgood

end Main

/-! ### 整合性チェック: 一般定理は有界証明書を包含する

`QueryGame.lean` の `native_decide` 証明書（N=6/7, ℓ=4 で深さ 1 は
勝てない）が、一般定理の系として（`native_decide` なしで）出ることを
確認する。`k₁*(6,4) = k₁*(7,4) = 2` の評価だけ `decide`。 -/

example : ¬ ∃ t : Tree 6 1, WinsAt 4 4 (0 : Fin 6) 1 t := by
  refine two_point_lower_bound (by norm_num) (lt_min (by norm_num) ?_)
  have h2 : 2 ≤ PeriodicTM.TwoPointCore.k1Star 6 4 := by
    rw [PeriodicTM.TwoPointCore.k1Star, Nat.le_find_iff]
    intro m hm
    have hm' : m = 0 ∨ m = 1 := by omega
    rcases hm' with rfl | rfl <;> decide
  omega

example : ¬ ∃ t : Tree 7 1, WinsAt 4 4 (0 : Fin 7) 1 t := by
  refine two_point_lower_bound (by norm_num) (lt_min (by norm_num) ?_)
  have h2 : 2 ≤ PeriodicTM.TwoPointCore.k1Star 7 4 := by
    rw [PeriodicTM.TwoPointCore.k1Star, Nat.le_find_iff]
    intro m hm
    have hm' : m = 0 ∨ m = 1 := by omega
    rcases hm' with rfl | rfl <;> decide
  omega

end PeriodicTM.ClaimA

#print axioms PeriodicTM.ClaimA.two_point_lower_bound

#print axioms PeriodicTM.ClaimA.type3_const_killed
#print axioms PeriodicTM.ClaimA.posZ_of_mem
#print axioms PeriodicTM.ClaimA.posO_of_mem
#print axioms PeriodicTM.ClaimA.stray_of_mem
