/-
FiniteOrderTM/TwoPointTransport.lean
— 葉での付け替え τ の構成と、グループ順埋め込みから具体状態への輸送
  （research/17 の修正方針の完結）

対局の終状態 `C : PathState N` に対し、グループ順ラベル列
（`AdvState.gpaths` の平坦化）を実際の頂点列 `C.used` へ写す置換 τ を
`extendPerm` で作る。すると
* `AdvState.edges`（グループ順の開示辺）は τ で `C.edges` にちょうど写り
  （`conc_edges_map`）、
* 主張A・同一軌道構成で得た任意の完成 `f₀` の共役 `τ f₀ τ⁻¹` は
  約束を満たし、`C.edges` を拡張する（`transport_completion`）。
  後者は `agreesC_of_extends` の前提そのものなので、完成が対局と
  一致することが従う。
τ は未開示ラベル・未使用点の対応 `ext₁ ↦ ext₂` を自由に追加できる
（`exists_leaf_transport`）。未開示点を軌道外や指定位置へ置く撃墜は
この自由度で行う。

**BUILD NOTE**: root（`FiniteOrderTM.lean`）非取込。検査は
`lake env lean FiniteOrderTM/TwoPointTransport.lean`。
-/
import FiniteOrderTM.TwoPointConcrete

namespace PeriodicTM.ClaimA

open Equiv Finset
open PeriodicTM.QueryGame (Tree GoodOutput Runs Valid WinsAt)

variable {N : ℕ}

/-! ### グループ順のパス一覧と辺の zip 表示 -/

/-- グループ順のパス一覧（0-パス・1-パス・迷いブロックの順）。
平坦化すると開示ラベルの列になる。 -/
def AdvState.gpaths (s : AdvState) : List (List ℕ) :=
  ((0 : ℕ) :: List.range' 2 s.k0) :: ((1 : ℕ) :: List.range' (2 + s.k0) s.k1)
    :: s.blocks

/-- `pathEdges` はパス頂点列の隣接対（`zip`）に等しい。 -/
theorem pathEdges_eq_zip (a next e : ℕ) :
    pathEdges a next e
      = (a :: List.range' next e).zip (List.range' next e) := by
  apply List.ext_getElem
  · simp [pathEdges, List.length_zip, List.length_range']
  · intro i h1 h2
    have hie : i < e := by simpa [pathEdges] using h1
    simp only [pathEdges, List.getElem_map, List.getElem_range,
      List.getElem_zip]
    cases i with
    | zero => simp [List.getElem_range']
    | succ j =>
      simp only [List.getElem_cons_succ, List.getElem_range',
        Prod.mk.injEq]
      constructor
      · rw [if_neg (by omega)]
        omega
      · omega

/-- `strayEdges` は迷いブロックの隣接対の平坦化に等しい。 -/
theorem strayEdges_eq_zip :
    ∀ (l : List ℕ) (next : ℕ),
      strayEdges next l
        = ((strayBlocks next l).map fun b => b.zip b.tail).flatten
  | [], _ => rfl
  | j :: rest, next => by
    have hblock : List.range' next (j + 1) = next :: List.range' (next + 1) j :=
      List.range'_succ
    simp only [strayEdges, strayBlocks, List.map_cons, List.flatten_cons]
    rw [strayEdges_eq_zip rest (next + 1 + j), pathEdges_eq_zip, hblock]
    rfl

/-- **開示辺の zip 表示**: `AdvState.edges` はグループ順パス一覧の
隣接対の平坦化。 -/
theorem edges_eq_zip (s : AdvState) :
    s.edges = (s.gpaths.map fun l => l.zip l.tail).flatten := by
  unfold AdvState.edges AdvState.gpaths AdvState.blocks
  rw [pathEdges_eq_zip, pathEdges_eq_zip, strayEdges_eq_zip]
  simp [List.append_assoc]

/-! ### グループ順ラベル列の性質 -/

/-- パスの長さは具体側と一致する。 -/
theorem gpaths_lengths [NeZero N] (C : PathState N) :
    C.toAdv.gpaths.map List.length = C.paths.map List.length := by
  simp only [AdvState.gpaths, PathState.paths, List.map_cons,
    List.length_cons, List.length_range']
  refine congrArg₂ _ ?_ (congrArg₂ _ ?_ ?_)
  · rfl
  · rfl
  · show (AdvState.blocks _).map _ = _
    rw [AdvState.blocks, strayBlocks_length_map]
    show (C.strays.map fun s => s.2.length).map (· + 1) = _
    simp [List.map_map, Function.comp_def]

/-- 開示ラベルはすべて `vertexCount` 未満。 -/
theorem gpaths_flatten_lt (s : AdvState) {M : ℕ} (hM : s.vertexCount ≤ M) :
    ∀ x ∈ s.gpaths.flatten, x < M := by
  have hvc : s.vertexCount
      = 2 + s.k0 + s.k1 + s.strays.sum + s.strays.length := rfl
  intro x hx
  simp only [AdvState.gpaths, List.flatten_cons] at hx
  rcases List.mem_append.mp hx with h | h
  · rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := List.mem_range'_1.mp h
      omega
  · rcases List.mem_append.mp h with h | h
    · rcases List.mem_cons.mp h with rfl | h
      · omega
      · have := List.mem_range'_1.mp h
        omega
    · obtain ⟨b, hb, hxb⟩ := List.mem_flatten.mp h
      have := blocks_mem_bound s hb hxb
      omega

/-- 開示ラベル列は Nodup（帯に分かれるから）。 -/
theorem gpaths_flatten_nodup (s : AdvState) : s.gpaths.flatten.Nodup := by
  have hvc : 2 + s.k0 + s.k1 ≤ s.vertexCount := by
    unfold AdvState.vertexCount
    omega
  have hA : ∀ x ∈ (0 : ℕ) :: List.range' 2 s.k0,
      x = 0 ∨ (2 ≤ x ∧ x < 2 + s.k0) := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | h
    · exact Or.inl rfl
    · have := List.mem_range'_1.mp h
      exact Or.inr (by omega)
  have hB : ∀ x ∈ (1 : ℕ) :: List.range' (2 + s.k0) s.k1,
      x = 1 ∨ (2 + s.k0 ≤ x ∧ x < 2 + s.k0 + s.k1) := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | h
    · exact Or.inl rfl
    · have := List.mem_range'_1.mp h
      exact Or.inr (by omega)
  have hF : ∀ x ∈ s.blocks.flatten,
      2 + s.k0 + s.k1 ≤ x ∧ x < s.vertexCount := by
    intro x hx
    obtain ⟨b, hb, hxb⟩ := List.mem_flatten.mp hx
    exact blocks_mem_bound s hb hxb
  have nA : ((0 : ℕ) :: List.range' 2 s.k0).Nodup :=
    List.nodup_cons.mpr ⟨fun h => by have := List.mem_range'_1.mp h; omega,
      List.nodup_range'⟩
  have nB : ((1 : ℕ) :: List.range' (2 + s.k0) s.k1).Nodup :=
    List.nodup_cons.mpr ⟨fun h => by have := List.mem_range'_1.mp h; omega,
      List.nodup_range'⟩
  have nF : s.blocks.flatten.Nodup :=
    List.nodup_flatten.mpr
      ⟨fun b hb => strayBlocks_nodup s.strays _ b hb,
        blocks_pairwise_disjoint s⟩
  have dBF : List.Disjoint ((1 : ℕ) :: List.range' (2 + s.k0) s.k1)
      s.blocks.flatten := by
    intro x hx hx'
    have := hB x hx
    have := hF x hx'
    omega
  have dABF : List.Disjoint ((0 : ℕ) :: List.range' 2 s.k0)
      (((1 : ℕ) :: List.range' (2 + s.k0) s.k1) ++ s.blocks.flatten) := by
    intro x hx hx'
    have h1 := hA x hx
    rcases List.mem_append.mp hx' with h | h
    · have := hB x h
      omega
    · have := hF x h
      omega
  show (((0 : ℕ) :: List.range' 2 s.k0) ++
    ((((1 : ℕ) :: List.range' (2 + s.k0) s.k1)) ++ s.blocks.flatten)).Nodup
  exact nA.append (nB.append nF dBF) dABF

/-! ### 平坦化からの分節と写像の対応 -/

/-- 平坦化どうしの対応から分節ごとの対応を復元する。 -/
theorem flatten_map_segments {α β : Type*} (φ : α → β) :
    ∀ (L : List (List α)) (M : List (List β)),
      L.map List.length = M.map List.length →
      L.flatten.map φ = M.flatten →
      L.map (List.map φ) = M
  | [], [], _, _ => rfl
  | [], _ :: _, hlen, _ => by simp at hlen
  | _ :: _, [], hlen, _ => by simp at hlen
  | l :: L, m :: M, hlen, hflat => by
    simp only [List.map_cons, List.cons.injEq] at hlen ⊢
    simp only [List.flatten_cons, List.map_append] at hflat
    have hlm : (l.map φ).length = m.length := by simp [hlen.1]
    obtain ⟨h1, h2⟩ := List.append_inj hflat hlm
    exact ⟨h1, flatten_map_segments φ L M hlen.2 h2⟩

/-- 対応リストの zip の各対で写像が成り立つ。 -/
theorem map_eq_zip_forall {α β : Type*} {φ : α → β} :
    ∀ {l : List α} {m : List β}, l.map φ = m →
      ∀ p ∈ l.zip m, φ p.1 = p.2
  | [], _, h, p, hp => by simp [← h] at hp
  | a :: l, _, rfl, p, hp => by
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · rfl
    · exact map_eq_zip_forall rfl p hp

/-- 隣接対は写像と可換。 -/
theorem zip_tail_map {α β : Type*} (φ : α → β) (l : List α) :
    (l.map φ).zip ((l.map φ).tail)
      = (l.zip l.tail).map (Prod.map φ φ) := by
  cases l with
  | nil => rfl
  | cons a t =>
    show (List.map φ (a :: t)).zip (List.map φ t) = _
    rw [List.zip_map]
    rfl

/-! ### 葉での τ の存在 -/

/-- **葉の付け替えの存在**: 不変量を満たす具体状態に対し、
グループ順ラベルを実頂点へ写し、指定点 0・1 を固定し、さらに
未開示ラベル `ext₁` を未使用点 `ext₂` へ写す置換 τ が存在する。 -/
theorem exists_leaf_transport [NeZero N] (C : PathState N) (hInv : C.Inv)
    (hN : 2 ≤ N) (ext₁ : List ℕ) (ext₂ : List (Fin N))
    (hext₁lt : ∀ u ∈ ext₁, u < N)
    (hext₁fresh : ∀ u ∈ ext₁, u ∉ C.toAdv.gpaths.flatten)
    (hext₁nd : ext₁.Nodup)
    (hext₂fresh : ∀ v ∈ ext₂, v ∉ C.used)
    (hext₂nd : ext₂.Nodup)
    (hlen : ext₁.length = ext₂.length) :
    ∃ τ : Perm (Fin N),
      τ 0 = 0 ∧ τ 1 = 1 ∧
      C.toAdv.gpaths.map (List.map (⇑τ ∘ Fin.ofNat N)) = C.paths ∧
      ∀ p ∈ ext₁.zip ext₂, τ (Fin.ofNat N p.1) = p.2 := by
  -- 頂点数の上界: used は Nodup なので長さ ≤ N
  have hvcN : C.toAdv.vertexCount ≤ N := by
    rw [← used_length]
    have := hInv.1.length_le_card
    simpa using this
  -- 対応リスト
  set Lg := C.toAdv.gpaths.flatten with hLg
  have hLglen : Lg.length = C.used.length := by
    rw [hLg, PathState.used, List.length_flatten, List.length_flatten,
      gpaths_lengths C]
  have hlt : ∀ x ∈ Lg ++ ext₁, x < N := by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact gpaths_flatten_lt C.toAdv hvcN x h
    · exact hext₁lt x h
  have hnd : (Lg ++ ext₁).Nodup :=
    (gpaths_flatten_nodup C.toAdv).append hext₁nd
      (fun x hx hx' => hext₁fresh x hx' hx)
  have h₁nd : ((Lg ++ ext₁).map (Fin.ofNat N)).Nodup := ofNat_injOn hlt hnd
  have h₂nd : (C.used ++ ext₂).Nodup :=
    hInv.1.append hext₂nd (fun v hv hv' => hext₂fresh v hv' hv)
  have h₁₂len : ((Lg ++ ext₁).map (Fin.ofNat N)).length
      = (C.used ++ ext₂).length := by
    simp only [List.length_map, List.length_append]
    omega
  set τ := PeriodicTM.Relabel.extendPerm
    ((Lg ++ ext₁).map (Fin.ofNat N)) (C.used ++ ext₂) with hτ
  have hmap := PeriodicTM.Relabel.extendPerm_map _ _ h₁nd h₂nd h₁₂len
  rw [← hτ, List.map_map, List.map_append] at hmap
  have hsplit := List.append_inj hmap (by
    simp only [List.length_map]
    exact hLglen)
  have hseg : C.toAdv.gpaths.map (List.map (⇑τ ∘ Fin.ofNat N)) = C.paths :=
    flatten_map_segments _ C.toAdv.gpaths C.paths (gpaths_lengths C)
      hsplit.1
  have hheads := hseg
  simp only [AdvState.gpaths, PathState.paths, List.map_cons,
    List.cons.injEq] at hheads
  refine ⟨τ, ?_, ?_, hseg, ?_⟩
  · -- τ 0 = 0
    have h0 : (⇑τ ∘ Fin.ofNat N) 0 = 0 := hheads.1.1
    rw [Function.comp_apply, ofNat_zero_eq_zero] at h0
    exact h0
  · -- τ 1 = 1
    have h1 : (⇑τ ∘ Fin.ofNat N) 1 = 1 := hheads.2.1.1
    rw [Function.comp_apply, ofNat_one_eq_one hN] at h1
    exact h1
  · -- ext の対応
    intro p hp
    exact map_eq_zip_forall hsplit.2 p hp

/-! ### 完成の輸送 -/

/-- 開示辺の輸送: 分節対応があれば、具体辺はグループ辺の像。 -/
theorem conc_edges_map [NeZero N] (C : PathState N) {φ : ℕ → Fin N}
    (hseg : C.toAdv.gpaths.map (List.map φ) = C.paths) :
    C.edges = C.toAdv.edges.map (Prod.map φ φ) := by
  rw [PathState.edges, ← hseg, edges_eq_zip, List.map_flatten,
    List.map_map, List.map_map]
  refine congrArg List.flatten (List.map_congr_left fun l _ => ?_)
  exact zip_tail_map φ l

/-- **完成の輸送**: `f₀` がグループ順埋め込みの完成なら、その共役
`τ f₀ τ⁻¹` は約束を満たし、具体状態の開示辺をすべて拡張する。 -/
theorem transport_completion [NeZero N] {ℓ : ℕ} (C : PathState N)
    {τ : Perm (Fin N)} (hτ0 : τ 0 = 0)
    (hseg : C.toAdv.gpaths.map (List.map (⇑τ ∘ Fin.ofNat N)) = C.paths)
    {f₀ : Perm (Fin N)} (hcomp : IsCompletion N ℓ C.toAdv f₀) :
    Valid ℓ ℓ (0 : Fin N) (τ * f₀ * τ⁻¹) ∧
      ∀ p ∈ C.edges, (τ * f₀ * τ⁻¹) p.1 = p.2 := by
  constructor
  · exact PeriodicTM.Relabel.valid_conj τ hτ0 ⟨hcomp.1, hcomp.2.1⟩
  · intro p hp
    rw [conc_edges_map C hseg] at hp
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hp
    exact PeriodicTM.Relabel.conj_extends (hcomp.2.2 e he)

end PeriodicTM.ClaimA

#print axioms PeriodicTM.ClaimA.edges_eq_zip
#print axioms PeriodicTM.ClaimA.gpaths_flatten_nodup
#print axioms PeriodicTM.ClaimA.exists_leaf_transport
#print axioms PeriodicTM.ClaimA.transport_completion
