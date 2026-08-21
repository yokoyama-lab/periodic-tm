/-
FiniteOrderTM/TwoPointSameCycle.lean
— 迷いパスの溢れに対応した同一軌道完成（research/18 の隙2の解消）

`TwoPointAdversary.sameCycleVerts` は全ブロックを 0-1 サイクルに
入れる構成で、領域内でも入り切らない状態がある（研究ノート 18）。
ここでは主張Aの `buildPerm` と同型の 2 サイクル構成にする:
* サイクルA（長さ ℓ）: `0 :: P₀ ++ gap(g) ++ 1 :: P₁ ++ bA ++ tail(e)`
  — 距離 `d = 1 + k₀ + g`、迷いAの頂点は位置 `d + (1 + k₁ + j)`。
* サイクルB（長さ `m ∣ ℓ`）: `bB ++ fillB` — 0 とも 1 とも別軌道。
距離 `d` と `d+1` は**同じ分割 (bA, bB)** で `g = 0, 1` を使う。
`g + e` が一定なので、サイクルAの充填ラベル区間もサイクルBも
両完成で一致する（未開示点の撃墜資源の共有に効く）。

詰め込みは `two_bin_pack` の 1 だけ精密な変種 `two_bin_pack'`
（`sum + max ≤ c₀ + c₁ + 1` で足りる）を使う。この 1 が無いと
領域内の状態（例: N=6, ℓ=4, 迷い1本）で詰め込みが出ない。

**BUILD NOTE**: root（`FiniteOrderTM.lean`）非取込。検査は
`lake env lean FiniteOrderTM/TwoPointSameCycle.lean`。
-/
import FiniteOrderTM.TwoPointClaimAGeneral

namespace PeriodicTM.ClaimA

open Equiv Finset

variable {N : ℕ}

/-! ### 2ビン詰めの精密化（+1） -/

/-- **2ビン貪欲詰めの精密な十分条件**: `sum + max ≤ c₀ + c₁ + 1` で
足りる（`two_bin_pack` より 1 緩い）。拒否の起きたビンの詰まり具合を
数えると、両ビンで拒否が起きるのは `2·max > c₀ + c₁ + 1` のときに
限るため。 -/
theorem two_bin_pack' {α : Type*} (size : α → ℕ) (items : List α) :
    ∀ c0 c1 : ℕ,
      (items.map size).sum + (items.map size).foldr max 0 ≤ c0 + c1 + 1 →
      ∃ l0 l1 : List α, (l0 ++ l1).Perm items ∧
        (l0.map size).sum ≤ c0 ∧ (l1.map size).sum ≤ c1 := by
  induction items with
  | nil => exact fun c0 c1 _ => ⟨[], [], by simp, by simp, by simp⟩
  | cons a t ih =>
    intro c0 c1 h
    simp only [List.map_cons, List.sum_cons, List.foldr_cons] at h
    have hM : (t.map size).foldr max 0
        ≤ max (size a) ((t.map size).foldr max 0) := le_max_right _ _
    have hMa : size a ≤ max (size a) ((t.map size).foldr max 0) :=
      le_max_left _ _
    by_cases ha0 : size a ≤ c0
    · obtain ⟨l0, l1, hp, h0, h1⟩ := ih (c0 - size a) c1 (by omega)
      refine ⟨a :: l0, l1, hp.cons a, ?_, h1⟩
      simp only [List.map_cons, List.sum_cons]
      omega
    · by_cases ha1 : size a ≤ c1
      · obtain ⟨l0, l1, hp, h0, h1⟩ := ih c0 (c1 - size a) (by omega)
        refine ⟨l0, a :: l1, List.perm_middle.trans (hp.cons a), h0, ?_⟩
        simp only [List.map_cons, List.sum_cons]
        omega
      · exfalso
        omega

/-! ### 2サイクルの頂点列 -/

/-- サイクルAの頂点列: `0`・P₀・gap 充填（`g` 個）・`1`・P₁・
迷いブロック bA・尾部充填（`e` 個）。距離は `d = 1 + k₀ + g`。 -/
def cycleAVerts (s : AdvState) (g : ℕ) (bA : List (List ℕ)) (e : ℕ) :
    List ℕ :=
  ((0 : ℕ) :: List.range' 2 s.k0) ++ List.range' s.vertexCount g ++
    ((1 : ℕ) :: List.range' (2 + s.k0) s.k1) ++ bA.flatten ++
    List.range' (s.vertexCount + g) e

/-- サイクルBの頂点列: 迷いブロック bB と充填（`fB` 個）。充填の開始は
`vc + c`（`c = g + e` は両距離で共通）なので、サイクルBは距離に依らず
同一。 -/
def cycleBVerts (s : AdvState) (c : ℕ) (bB : List (List ℕ)) (fB : ℕ) :
    List ℕ :=
  bB.flatten ++ List.range' (s.vertexCount + c) fB

theorem cycleAVerts_length (s : AdvState) (g : ℕ) (bA : List (List ℕ))
    (e : ℕ) :
    (cycleAVerts s g bA e).length
      = 2 + s.k0 + s.k1 + g + (bA.map List.length).sum + e := by
  unfold cycleAVerts
  simp [List.length_append, List.length_range', List.length_flatten]
  omega

theorem cycleBVerts_length (s : AdvState) (c : ℕ) (bB : List (List ℕ))
    (fB : ℕ) :
    (cycleBVerts s c bB fB).length = (bB.map List.length).sum + fB := by
  unfold cycleBVerts
  simp [List.length_append, List.length_range', List.length_flatten]

/-! ### 帯の値域と Nodup -/

section Bands

/-- サイクルAの頂点の所属（5 つの帯）。 -/
theorem mem_cycleAVerts (s : AdvState) (g : ℕ) (bA : List (List ℕ)) (e : ℕ)
    (hbA : ∀ b ∈ bA, ∀ x ∈ b, 2 + s.k0 + s.k1 ≤ x ∧ x < s.vertexCount) :
    ∀ x ∈ cycleAVerts s g bA e,
      (x = 0 ∨ (2 ≤ x ∧ x < 2 + s.k0)) ∨
      (s.vertexCount ≤ x ∧ x < s.vertexCount + g) ∨
      (x = 1 ∨ (2 + s.k0 ≤ x ∧ x < 2 + s.k0 + s.k1)) ∨
      (2 + s.k0 + s.k1 ≤ x ∧ x < s.vertexCount ∧ ∃ b ∈ bA, x ∈ b) ∨
      (s.vertexCount + g ≤ x ∧ x < s.vertexCount + g + e) := by
  intro x hx
  unfold cycleAVerts at hx
  rcases List.mem_append.mp hx with h | h
  swap
  · exact Or.inr (Or.inr (Or.inr (Or.inr (List.mem_range'_1.mp h))))
  rcases List.mem_append.mp h with h | h
  swap
  · obtain ⟨b, hb, hxb⟩ := List.mem_flatten.mp h
    have := hbA b hb x hxb
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨this.1, this.2, b, hb, hxb⟩)))
  rcases List.mem_append.mp h with h | h
  swap
  · rcases List.mem_cons.mp h with rfl | h
    · exact Or.inr (Or.inr (Or.inl (Or.inl rfl)))
    · have := List.mem_range'_1.mp h
      exact Or.inr (Or.inr (Or.inl (Or.inr ⟨by omega, by omega⟩)))
  rcases List.mem_append.mp h with h | h
  · rcases List.mem_cons.mp h with rfl | h
    · exact Or.inl (Or.inl rfl)
    · have := List.mem_range'_1.mp h
      exact Or.inl (Or.inr ⟨by omega, by omega⟩)
  · exact Or.inr (Or.inl (List.mem_range'_1.mp h))

/-- サイクルAは Nodup。 -/
theorem cycleAVerts_nodup (s : AdvState) (g : ℕ) (bA : List (List ℕ))
    (e : ℕ) (hbmem : ∀ b ∈ bA, b ∈ s.blocks)
    (hbnd : bA.Pairwise List.Disjoint) (hbdup : ∀ b ∈ bA, b.Nodup) :
    (cycleAVerts s g bA e).Nodup := by
  have hvc : 2 + s.k0 + s.k1 ≤ s.vertexCount := by
    have : s.vertexCount = 2 + s.k0 + s.k1 + s.strays.sum + s.strays.length :=
      rfl
    omega
  have hbA : ∀ b ∈ bA, ∀ x ∈ b, 2 + s.k0 + s.k1 ≤ x ∧ x < s.vertexCount :=
    fun b hb x hx => blocks_mem_bound s (hbmem b hb) hx
  have hF : ∀ x ∈ bA.flatten, 2 + s.k0 + s.k1 ≤ x ∧ x < s.vertexCount := by
    intro x hx
    obtain ⟨b, hb, hxb⟩ := List.mem_flatten.mp hx
    exact hbA b hb x hxb
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
  have hG : ∀ x ∈ List.range' s.vertexCount g,
      s.vertexCount ≤ x ∧ x < s.vertexCount + g := fun x hx =>
    List.mem_range'_1.mp hx
  have hT : ∀ x ∈ List.range' (s.vertexCount + g) e,
      s.vertexCount + g ≤ x ∧ x < s.vertexCount + g + e := fun x hx =>
    List.mem_range'_1.mp hx
  have nA : ((0 : ℕ) :: List.range' 2 s.k0).Nodup :=
    List.nodup_cons.mpr ⟨fun h => by have := List.mem_range'_1.mp h; omega,
      List.nodup_range'⟩
  have nB : ((1 : ℕ) :: List.range' (2 + s.k0) s.k1).Nodup :=
    List.nodup_cons.mpr ⟨fun h => by have := List.mem_range'_1.mp h; omega,
      List.nodup_range'⟩
  have nF : bA.flatten.Nodup := List.nodup_flatten.mpr ⟨hbdup, hbnd⟩
  unfold cycleAVerts
  refine (((nA.append List.nodup_range' ?_).append nB ?_).append nF
    ?_).append List.nodup_range' ?_
  · intro x hx hx'
    have := hA x hx
    have := hG x hx'
    omega
  · intro x hx hx'
    have := hB x hx'
    rcases List.mem_append.mp hx with h | h
    · have := hA x h
      omega
    · have := hG x h
      omega
  · intro x hx hx'
    have := hF x hx'
    rcases List.mem_append.mp hx with h | h
    · rcases List.mem_append.mp h with h | h
      · have := hA x h
        omega
      · have := hG x h
        omega
    · have := hB x h
      omega
  · intro x hx hx'
    have := hT x hx'
    rcases List.mem_append.mp hx with h | h
    · rcases List.mem_append.mp h with h | h
      · rcases List.mem_append.mp h with h | h
        · have := hA x h
          omega
        · have := hG x h
          omega
      · have := hB x h
        omega
    · have := hF x h
      omega

/-- サイクルBは Nodup。 -/
theorem cycleBVerts_nodup (s : AdvState) (c : ℕ) (bB : List (List ℕ))
    (fB : ℕ) (hbmem : ∀ b ∈ bB, b ∈ s.blocks)
    (hbnd : bB.Pairwise List.Disjoint) (hbdup : ∀ b ∈ bB, b.Nodup) :
    (cycleBVerts s c bB fB).Nodup := by
  have hF : ∀ x ∈ bB.flatten, 2 + s.k0 + s.k1 ≤ x ∧ x < s.vertexCount := by
    intro x hx
    obtain ⟨b, hb, hxb⟩ := List.mem_flatten.mp hx
    exact blocks_mem_bound s (hbmem b hb) hxb
  unfold cycleBVerts
  refine (List.nodup_flatten.mpr ⟨hbdup, hbnd⟩).append List.nodup_range' ?_
  intro x hx hx'
  have h1 := hF x hx
  have h2 := List.mem_range'_1.mp hx'
  omega

/-- サイクルAとサイクルBは頂点を共有しない。 -/
theorem cycleAB_disjoint (s : AdvState) (g e fB : ℕ)
    (bA bB : List (List ℕ))
    (hbA : ∀ b ∈ bA, b ∈ s.blocks) (hbB : ∀ b ∈ bB, b ∈ s.blocks)
    (hcross : ∀ b ∈ bA, ∀ c ∈ bB, List.Disjoint b c) :
    List.Disjoint (cycleAVerts s g bA e) (cycleBVerts s (g + e) bB fB) := by
  have hvc : 2 + s.k0 + s.k1 ≤ s.vertexCount := by
    have : s.vertexCount = 2 + s.k0 + s.k1 + s.strays.sum + s.strays.length :=
      rfl
    omega
  have hbAbd : ∀ b ∈ bA, ∀ x ∈ b, 2 + s.k0 + s.k1 ≤ x ∧ x < s.vertexCount :=
    fun b hb x hx => blocks_mem_bound s (hbA b hb) hx
  have hbBbd : ∀ b ∈ bB, ∀ x ∈ b, 2 + s.k0 + s.k1 ≤ x ∧ x < s.vertexCount :=
    fun b hb x hx => blocks_mem_bound s (hbB b hb) hx
  intro x hx hx'
  unfold cycleBVerts at hx'
  rcases List.mem_append.mp hx' with hB | hB
  · -- x は bB のブロックの中
    obtain ⟨c', hc', hxc'⟩ := List.mem_flatten.mp hB
    rcases mem_cycleAVerts s g bA e hbAbd x hx with h | h | h | h | h
    · have := (hbBbd c' hc' x hxc').1
      rcases h with rfl | h <;> omega
    · have := (hbBbd c' hc' x hxc').2
      omega
    · have := (hbBbd c' hc' x hxc').1
      rcases h with rfl | h <;> omega
    · obtain ⟨_, _, b, hb, hxb⟩ := h
      exact hcross b hb c' hc' hxb hxc'
    · have := (hbBbd c' hc' x hxc').2
      omega
  · -- x はサイクルBの充填 `[vc + g + e, ...)` の中
    have h2 := List.mem_range'_1.mp hB
    rcases mem_cycleAVerts s g bA e hbAbd x hx with h | h | h | h | h
    · rcases h with rfl | h <;> omega
    · omega
    · rcases h with rfl | h <;> omega
    · omega
    · omega

end Bands

/-! ### 開示辺の振り分け（隣接） -/

/-- すべての開示辺はサイクルAかサイクルBの隣接になる。 -/
theorem edges_isAdj2 (s : AdvState) (g e fB : ℕ) (bA bB : List (List ℕ))
    (hsplit : ∀ b ∈ s.blocks, b ∈ bA ∨ b ∈ bB) :
    ∀ p ∈ s.edges,
      IsAdj (cycleAVerts s g bA e) p.1 p.2 ∨
      IsAdj (cycleBVerts s (g + e) bB fB) p.1 p.2 := by
  intro p hp
  unfold AdvState.edges at hp
  unfold cycleAVerts cycleBVerts
  rcases List.mem_append.mp hp with h | h
  · rcases List.mem_append.mp h with h | h
    · -- P₀ の辺: 先頭ブロックの隣接
      exact Or.inl
        (pathEdges_isAdj h).append_right.append_right.append_right.append_right
    · -- P₁ の辺: `(A₀ ++ G) ++ B₀` の中
      exact Or.inl
        (pathEdges_isAdj h).append_left.append_right.append_right
  · obtain ⟨b, hb, hadj⟩ := strayEdges_mem_block s.strays (2 + s.k0 + s.k1) p h
    rcases hsplit b hb with hbA | hbB
    · exact Or.inl (hadj.flatten hbA).append_left.append_right
    · exact Or.inr (hadj.flatten hbB).append_right

/-! ### 2サイクル完成の接着 -/

/-- 同一軌道完成（2サイクル版）: サイクルAとサイクルBの `formPerm` の積。 -/
def sameCyclePerm2 (N : ℕ) [NeZero N] (s : AdvState) (g : ℕ)
    (bA : List (List ℕ)) (e : ℕ) (bB : List (List ℕ)) (fB : ℕ) :
    Perm (Fin N) :=
  ((cycleAVerts s g bA e).map (Fin.ofNat N)).formPerm *
    ((cycleBVerts s (g + e) bB fB).map (Fin.ofNat N)).formPerm

section Glue

variable [NeZero N]

/-- `0` はサイクルAの先頭。 -/
theorem cycleAVerts_getElem?_zero (s : AdvState) (g : ℕ)
    (bA : List (List ℕ)) (e : ℕ) :
    (cycleAVerts s g bA e)[0]? = some 0 := by
  unfold cycleAVerts
  simp [List.cons_append]

/-- `1` はサイクルAの位置 `1 + k₀ + g`（= 距離 `d`）。 -/
theorem cycleAVerts_getElem?_one (s : AdvState) (g : ℕ)
    (bA : List (List ℕ)) (e : ℕ) :
    (cycleAVerts s g bA e)[1 + s.k0 + g]? = some 1 := by
  unfold cycleAVerts
  have h1 : ((0 : ℕ) :: List.range' 2 s.k0).length = 1 + s.k0 := by
    simp [List.length_range']
    omega
  rw [List.append_assoc, List.append_assoc, List.append_assoc,
    List.getElem?_append_right (by omega), h1,
    List.getElem?_append_right (by simp [List.length_range'])]
  have hidx : 1 + s.k0 + g - (1 + s.k0) - (List.range' s.vertexCount g).length
      = 0 := by
    simp [List.length_range']
  rw [hidx]
  simp

/-- 迷いAの第 `j` 頂点はサイクルAの位置 `2 + k₀ + k₁ + g + j`。 -/
theorem cycleAVerts_getElem?_stray (s : AdvState) (g : ℕ)
    (bA : List (List ℕ)) (e : ℕ) (j : ℕ) (hj : j < bA.flatten.length) :
    (cycleAVerts s g bA e)[2 + s.k0 + s.k1 + g + j]? = bA.flatten[j]? := by
  unfold cycleAVerts
  have h1 : ((0 : ℕ) :: List.range' 2 s.k0).length = 1 + s.k0 := by
    simp [List.length_range']
    omega
  have h2 : ((1 : ℕ) :: List.range' (2 + s.k0) s.k1).length = 1 + s.k1 := by
    simp [List.length_range']
    omega
  rw [List.append_assoc, List.append_assoc, List.append_assoc,
    List.getElem?_append_right (by omega), h1,
    List.getElem?_append_right (by simp [List.length_range']; omega),
    List.getElem?_append_right (by simp [List.length_range', h2]; omega)]
  have hidx : 2 + s.k0 + s.k1 + g + j - (1 + s.k0)
      - (List.range' s.vertexCount g).length
      - ((1 : ℕ) :: List.range' (2 + s.k0) s.k1).length = j := by
    simp [List.length_range', h2]
    omega
  rw [hidx, List.getElem?_append_left hj]

/-- 尾部充填の第 `t` 頂点（ラベル `vc + g + t`）はサイクルAの位置
`2 + k₀ + k₁ + g + ΣA + t`。 -/
theorem cycleAVerts_getElem?_tail (s : AdvState) (g : ℕ)
    (bA : List (List ℕ)) (e : ℕ) (t : ℕ) (ht : t < e) :
    (cycleAVerts s g bA e)[2 + s.k0 + s.k1 + g + bA.flatten.length + t]?
      = some (s.vertexCount + g + t) := by
  unfold cycleAVerts
  have h1 : ((0 : ℕ) :: List.range' 2 s.k0).length = 1 + s.k0 := by
    simp [List.length_range']
    omega
  have h2 : ((1 : ℕ) :: List.range' (2 + s.k0) s.k1).length = 1 + s.k1 := by
    simp [List.length_range']
    omega
  rw [List.append_assoc, List.append_assoc, List.append_assoc,
    List.getElem?_append_right (by omega), h1,
    List.getElem?_append_right (by simp [List.length_range']; omega),
    List.getElem?_append_right (by simp [List.length_range', h2]; omega),
    List.getElem?_append_right (by simp [List.length_range', h2]; omega)]
  have hidx : 2 + s.k0 + s.k1 + g + bA.flatten.length + t - (1 + s.k0)
      - (List.range' s.vertexCount g).length
      - ((1 : ℕ) :: List.range' (2 + s.k0) s.k1).length
      - bA.flatten.length = t := by
    simp [List.length_range', h2]
    omega
  rw [hidx]
  simp [ht]

/-- **位置の読み出し**: サイクルAの第 `i` 頂点は `f^i(0)` の像。 -/
theorem sameCyclePerm2_pow_pos {ℓ : ℕ} (s : AdvState) (g : ℕ)
    (bA : List (List ℕ)) (e : ℕ) (bB : List (List ℕ)) (fB : ℕ)
    (hndA : (cycleAVerts s g bA e).Nodup)
    (hdisj : List.Disjoint (cycleAVerts s g bA e)
      (cycleBVerts s (g + e) bB fB))
    (hltA : ∀ x ∈ cycleAVerts s g bA e, x < N)
    (hltB : ∀ x ∈ cycleBVerts s (g + e) bB fB, x < N)
    (hlenA : (cycleAVerts s g bA e).length = ℓ)
    (i : ℕ) (hi : i < ℓ) {v : ℕ}
    (hv : (cycleAVerts s g bA e)[i]? = some v) :
    ((sameCyclePerm2 N s g bA e bB fB) ^ i) (Fin.ofNat N 0)
      = Fin.ofNat N v := by
  have hL0nd := ofNat_injOn (N := N) hltA hndA
  have hLd := ofNat_disjoint (N := N) hltA hltB hdisj
  have h0idx : 0 < (cycleAVerts s g bA e).length := by omega
  have hiidx : i < (cycleAVerts s g bA e).length := by omega
  set L := (cycleAVerts s g bA e).map (Fin.ofNat N) with hL
  have h0? : L[0]? = some (Fin.ofNat N 0) := by
    rw [hL, List.getElem?_map, cycleAVerts_getElem?_zero]
    rfl
  have hv? : L[i]? = some (Fin.ofNat N v) := by
    rw [hL, List.getElem?_map, hv]
    rfl
  have h0 := List.getElem?_eq_getElem (l := L) (i := 0)
    (by rw [hL, List.length_map]; exact h0idx)
  have hvL := List.getElem?_eq_getElem (l := L) (i := i)
    (by rw [hL, List.length_map]; exact hiidx)
  rw [h0?] at h0
  rw [hv?] at hvL
  have h0mem : Fin.ofNat N 0 ∈ L := (Option.some.inj h0) ▸ List.getElem_mem _
  unfold sameCyclePerm2
  rw [mul_pow_apply_of_mem hLd i h0mem]
  have key := List.formPerm_pow_apply_getElem L hL0nd i 0
    (by rw [hL, List.length_map]; exact h0idx)
  have hmod : (0 + i) % L.length = i := by
    rw [Nat.zero_add, hL, List.length_map, hlenA]
    exact Nat.mod_eq_of_lt hi
  simp only [hmod] at key
  rw [Option.some.inj h0, Option.some.inj hvL]
  exact key

/-- **接着**: 構造仮定のもとで `sameCyclePerm2` は状態の完成。 -/
theorem sameCyclePerm2_isCompletion {ℓ m : ℕ} (s : AdvState) (g : ℕ)
    (bA : List (List ℕ)) (e : ℕ) (bB : List (List ℕ)) (fB : ℕ)
    (hlenA : (cycleAVerts s g bA e).length = ℓ)
    (hlenB : (cycleBVerts s (g + e) bB fB).length = m)
    (hmdvd : m ∣ ℓ)
    (hndA : (cycleAVerts s g bA e).Nodup)
    (hndB : (cycleBVerts s (g + e) bB fB).Nodup)
    (hdisj : List.Disjoint (cycleAVerts s g bA e)
      (cycleBVerts s (g + e) bB fB))
    (hltA : ∀ x ∈ cycleAVerts s g bA e, x < N)
    (hltB : ∀ x ∈ cycleBVerts s (g + e) bB fB, x < N)
    (hsplit : ∀ b ∈ s.blocks, b ∈ bA ∨ b ∈ bB) :
    IsCompletion N ℓ s (sameCyclePerm2 N s g bA e bB fB) := by
  have hL0nd := ofNat_injOn (N := N) hltA hndA
  have hL1nd := ofNat_injOn (N := N) hltB hndB
  have hLd := ofNat_disjoint (N := N) hltA hltB hdisj
  have h0mem : (0 : Fin N) ∈ (cycleAVerts s g bA e).map (Fin.ofNat N) := by
    have h : (0 : ℕ) ∈ cycleAVerts s g bA e := by
      unfold cycleAVerts
      simp
    have := List.mem_map_of_mem (f := Fin.ofNat N) h
    rwa [ofNat_zero_eq_zero] at this
  unfold sameCyclePerm2
  refine ⟨?_, ?_, ?_⟩
  · exact formPerm_mul_pow_eq_one hL0nd hL1nd hLd
      (by rw [List.length_map, hlenA])
      (by rw [List.length_map, hlenB]; exact hmdvd)
  · simpa [List.length_map, hlenA] using orbit_card hL0nd hLd h0mem
  · intro p hp
    rcases edges_isAdj2 s g e fB bA bB hsplit p hp with h | h
    · have hadj := h.map (Fin.ofNat N)
      rw [mul_apply_of_mem_left hLd hadj.mem_left]
      exact formPerm_of_adjacent hL0nd hadj
    · have hadj := h.map (Fin.ofNat N)
      rw [mul_apply_of_mem_right hLd hadj.mem_left]
      exact formPerm_of_adjacent hL1nd hadj

/-- **軌道外**: サイクルAに乗らない点は `0` とも `1` とも別軌道。 -/
theorem sameCyclePerm2_offOrbit (s : AdvState) (g : ℕ)
    (bA : List (List ℕ)) (e : ℕ) (bB : List (List ℕ)) (fB : ℕ)
    (hndA : (cycleAVerts s g bA e).Nodup)
    (hdisj : List.Disjoint (cycleAVerts s g bA e)
      (cycleBVerts s (g + e) bB fB))
    (hltA : ∀ x ∈ cycleAVerts s g bA e, x < N)
    (hltB : ∀ x ∈ cycleBVerts s (g + e) bB fB, x < N)
    (hN : 2 ≤ N)
    {y : Fin N} (hy : y ∉ (cycleAVerts s g bA e).map (Fin.ofNat N)) :
    ¬ (sameCyclePerm2 N s g bA e bB fB).SameCycle 0 y ∧
    ¬ (sameCyclePerm2 N s g bA e bB fB).SameCycle 1 y := by
  have hL0nd := ofNat_injOn (N := N) hltA hndA
  have hLd := ofNat_disjoint (N := N) hltA hltB hdisj
  have h0mem : (0 : Fin N) ∈ (cycleAVerts s g bA e).map (Fin.ofNat N) := by
    have h : (0 : ℕ) ∈ cycleAVerts s g bA e := by
      unfold cycleAVerts
      simp
    have := List.mem_map_of_mem (f := Fin.ofNat N) h
    rwa [ofNat_zero_eq_zero] at this
  have h1mem : (1 : Fin N) ∈ (cycleAVerts s g bA e).map (Fin.ofNat N) := by
    have h : (1 : ℕ) ∈ cycleAVerts s g bA e := by
      unfold cycleAVerts
      simp
    have := List.mem_map_of_mem (f := Fin.ofNat N) h
    rwa [ofNat_one_eq_one hN] at this
  constructor
  · exact not_sameCycle_of_notMem hLd h0mem hy
  · exact not_sameCycle_of_notMem hLd h1mem hy

end Glue

/-! ### 領域条件からのデータ束

下界の葉の場合分け（research/18 の表）が必要とする一式:
距離 `d`・`d+1` の 2 つの同一軌道完成、迷いブロックの割当
（迷いAは位置 `d + (1 + k₁ + j)`、迷いBは両軌道の外）、
未開示点の撃墜資源（軌道外ラベル `u` または共通尾部ラベル `w`）。 -/

/-- 2 距離の同一軌道完成と撃墜資源の束。 -/
structure SameCycleData (N ℓ : ℕ) [NeZero N] (s : AdvState) where
  d : ℕ
  bA : List (List ℕ)
  bB : List (List ℕ)
  f₀ : Perm (Fin N)
  f₁ : Perm (Fin N)
  hd : d = s.k0 + 1
  cover : ∀ b ∈ s.blocks, b ∈ bA ∨ b ∈ bB
  hSumA : bA.flatten.length + 3 + s.k0 + s.k1 ≤ ℓ
  comp₀ : IsCompletion N ℓ s f₀
  comp₁ : IsCompletion N ℓ s f₁
  dist₀ : (1 : Fin N) = (f₀ ^ d) 0
  dist₁ : (1 : Fin N) = (f₁ ^ (d + 1)) 0
  strayA₀ : ∀ j, (hj : j < bA.flatten.length) →
    (f₀ ^ (d + (1 + s.k1 + j))) (0 : Fin N) = Fin.ofNat N (bA.flatten[j]'hj)
  strayA₁ : ∀ j, (hj : j < bA.flatten.length) →
    (f₁ ^ ((d + 1) + (1 + s.k1 + j))) (0 : Fin N)
      = Fin.ofNat N (bA.flatten[j]'hj)
  offB₀ : ∀ x ∈ bB.flatten,
    ¬ f₀.SameCycle 0 (Fin.ofNat N x) ∧ ¬ f₀.SameCycle 1 (Fin.ofNat N x)
  offB₁ : ∀ x ∈ bB.flatten,
    ¬ f₁.SameCycle 0 (Fin.ofNat N x) ∧ ¬ f₁.SameCycle 1 (Fin.ofNat N x)
  resource :
    (∃ u : ℕ, s.vertexCount ≤ u ∧ u < N ∧
      (¬ f₀.SameCycle 0 (Fin.ofNat N u) ∧ ¬ f₀.SameCycle 1 (Fin.ofNat N u)) ∧
      (¬ f₁.SameCycle 0 (Fin.ofNat N u) ∧ ¬ f₁.SameCycle 1 (Fin.ofNat N u))) ∨
    (∃ w : ℕ, s.vertexCount ≤ w ∧ w < N ∧
      (f₀ ^ (ℓ - 1)) (0 : Fin N) = Fin.ofNat N w ∧
      (f₁ ^ (ℓ - 1)) (0 : Fin N) = Fin.ofNat N w)

section Exists

variable [NeZero N]

/-- `Fin.ofNat` の像に入らないこと（値域内の非所属から）。 -/
theorem ofNat_notMem_map {l : List ℕ} (hl : ∀ x ∈ l, x < N) {u : ℕ}
    (hu : u < N) (hnot : u ∉ l) :
    Fin.ofNat N u ∉ l.map (Fin.ofNat N) := by
  intro hmem
  obtain ⟨x', hx', heq⟩ := List.mem_map.mp hmem
  have hval : x' % N = u % N := by
    have := congrArg Fin.val heq
    simpa [Fin.ofNat] using this
  rw [Nat.mod_eq_of_lt (hl x' hx'), Nat.mod_eq_of_lt hu] at hval
  exact hnot (hval ▸ hx')

/-- **データ束の存在**: 下界領域の任意の状態に対し、`SameCycleData` が
取れる。 -/
theorem exists_sameCycleData {ℓ : ℕ} (s : AdvState)
    (hfit : s.Fits N) (hreg : InLowerRegion N ℓ s) (hℓ : 3 ≤ ℓ) :
    Nonempty (SameCycleData N ℓ s) := by
  classical
  -- 領域条件の算術
  unfold InLowerRegion at hreg
  have hq2 : s.q < ℓ - 2 := lt_of_lt_of_le hreg (min_le_left _ _)
  have hqk : s.q < PeriodicTM.TwoPointCore.k1Star N ℓ :=
    lt_of_lt_of_le hreg (min_le_right _ _)
  have hnk := PeriodicTM.TwoPointCore.not_kills_of_lt_k1Star hqk
  unfold PeriodicTM.TwoPointCore.Kills at hnk
  push_neg at hnk
  obtain ⟨m, hmℓ, hmq, hmdvd, hmN⟩ := hnk
  have hq3 : s.q + 3 ≤ ℓ := by omega
  have hqdef : s.q = s.k0 + s.k1 + s.strays.sum := rfl
  have hvc : s.vertexCount
      = 2 + s.k0 + s.k1 + s.strays.sum + s.strays.length := rfl
  have hrq : s.strays.length ≤ s.strays.sum := length_le_sum hfit.1
  have hℓN : ℓ + m ≤ N := by omega
  have hN2 : 2 ≤ N := by omega
  -- 詰め込み
  have hcap := capacity_ineq s hfit.1 hq3 (by omega)
  obtain ⟨bA, bB, hperm, hSumA, hSumB⟩ :=
    two_bin_pack' List.length s.blocks (ℓ - 3 - s.k0 - s.k1) m (by omega)
  have hpw : (bA ++ bB).Pairwise List.Disjoint :=
    (hperm.pairwise_iff (@fun _ _ h => List.Disjoint.symm h)).mpr
      (blocks_pairwise_disjoint s)
  obtain ⟨hpA, hpB, hcross⟩ := List.pairwise_append.mp hpw
  have hmemA : ∀ b ∈ bA, b ∈ s.blocks :=
    fun b hb => hperm.mem_iff.mp (List.mem_append.mpr (Or.inl hb))
  have hmemB : ∀ b ∈ bB, b ∈ s.blocks :=
    fun b hb => hperm.mem_iff.mp (List.mem_append.mpr (Or.inr hb))
  have hcover : ∀ b ∈ s.blocks, b ∈ bA ∨ b ∈ bB :=
    fun b hb => List.mem_append.mp (hperm.mem_iff.mpr hb)
  have hsumAB : (bA.map List.length).sum + (bB.map List.length).sum
      = s.strays.sum + s.strays.length := by
    have hsum : ((bA ++ bB).map List.length).sum
        = (s.blocks.map List.length).sum := (hperm.map List.length).sum_eq
    rw [List.map_append, List.sum_append] at hsum
    rw [hsum, blocks_length_sum]
  have hbdupA : ∀ b ∈ bA, b.Nodup :=
    fun b hb => strayBlocks_nodup s.strays _ b (hmemA b hb)
  have hbdupB : ∀ b ∈ bB, b.Nodup :=
    fun b hb => strayBlocks_nodup s.strays _ b (hmemB b hb)
  have hbAbd : ∀ b ∈ bA, ∀ x ∈ b, 2 + s.k0 + s.k1 ≤ x ∧ x < s.vertexCount :=
    fun b hb x hx => blocks_mem_bound s (hmemA b hb) hx
  have hbBbd : ∀ b ∈ bB, ∀ x ∈ b, 2 + s.k0 + s.k1 ≤ x ∧ x < s.vertexCount :=
    fun b hb x hx => blocks_mem_bound s (hmemB b hb) hx
  -- 記号
  set SA := (bA.map List.length).sum with hSA
  have hflatA : bA.flatten.length = SA := by
    rw [List.length_flatten, hSA]
  set c := ℓ - 2 - s.k0 - s.k1 - SA with hc
  have hc1 : 1 ≤ c := by omega
  set fB := m - (bB.map List.length).sum with hfB
  have hvcc : s.vertexCount + c = ℓ + (bB.map List.length).sum := by omega
  have htot : s.vertexCount + c + fB = ℓ + m := by omega
  set e₀ := c with he₀
  set e₁ := c - 1 with he₁
  have hge₀ : (0 : ℕ) + e₀ = c := by omega
  have hge₁ : (1 : ℕ) + e₁ = c := by omega
  -- 長さ
  have hlenA₀ : (cycleAVerts s 0 bA e₀).length = ℓ := by
    rw [cycleAVerts_length]
    omega
  have hlenA₁ : (cycleAVerts s 1 bA e₁).length = ℓ := by
    rw [cycleAVerts_length]
    omega
  have hlenB : (cycleBVerts s c bB fB).length = m := by
    rw [cycleBVerts_length]
    omega
  -- 値域
  have hltA : ∀ g e, g + e = c → ∀ x ∈ cycleAVerts s g bA e, x < N := by
    intro g e hge x hx
    rcases mem_cycleAVerts s g bA e hbAbd x hx with h | h | h | h | h
    · rcases h with rfl | h <;> omega
    · omega
    · rcases h with rfl | h <;> omega
    · omega
    · omega
  have hltB : ∀ x ∈ cycleBVerts s c bB fB, x < N := by
    intro x hx
    unfold cycleBVerts at hx
    rcases List.mem_append.mp hx with h | h
    · obtain ⟨b, hb, hxb⟩ := List.mem_flatten.mp h
      have := hbBbd b hb x hxb
      omega
    · have := List.mem_range'_1.mp h
      omega
  -- Nodup と相互素
  have hndA₀ := cycleAVerts_nodup s 0 bA e₀ hmemA hpA hbdupA
  have hndA₁ := cycleAVerts_nodup s 1 bA e₁ hmemA hpA hbdupA
  have hndB := cycleBVerts_nodup s c bB fB hmemB hpB hbdupB
  have hdisj₀ : List.Disjoint (cycleAVerts s 0 bA e₀)
      (cycleBVerts s ((0 : ℕ) + e₀) bB fB) := by
    rw [hge₀]
    have := cycleAB_disjoint s 0 e₀ fB bA bB hmemA hmemB hcross
    rwa [hge₀] at this
  have hdisj₁ : List.Disjoint (cycleAVerts s 1 bA e₁)
      (cycleBVerts s ((1 : ℕ) + e₁) bB fB) := by
    rw [hge₁]
    have := cycleAB_disjoint s 1 e₁ fB bA bB hmemA hmemB hcross
    rwa [hge₁] at this
  have hltB₀ : ∀ x ∈ cycleBVerts s ((0 : ℕ) + e₀) bB fB, x < N := by
    rw [hge₀]
    exact hltB
  have hltB₁ : ∀ x ∈ cycleBVerts s ((1 : ℕ) + e₁) bB fB, x < N := by
    rw [hge₁]
    exact hltB
  have hlenB₀ : (cycleBVerts s ((0 : ℕ) + e₀) bB fB).length = m := by
    rw [hge₀]
    exact hlenB
  have hlenB₁ : (cycleBVerts s ((1 : ℕ) + e₁) bB fB).length = m := by
    rw [hge₁]
    exact hlenB
  have hltA₀ := hltA 0 e₀ (by omega)
  have hltA₁ := hltA 1 e₁ (by omega)
  -- 完成
  set f₀ := sameCyclePerm2 N s 0 bA e₀ bB fB with hf₀
  set f₁ := sameCyclePerm2 N s 1 bA e₁ bB fB with hf₁
  have comp₀ : IsCompletion N ℓ s f₀ :=
    sameCyclePerm2_isCompletion s 0 bA e₀ bB fB hlenA₀ hlenB₀ hmdvd
      hndA₀ (by rw [hge₀]; exact hndB) hdisj₀ hltA₀ hltB₀ hcover
  have comp₁ : IsCompletion N ℓ s f₁ :=
    sameCyclePerm2_isCompletion s 1 bA e₁ bB fB hlenA₁ hlenB₁ hmdvd
      hndA₁ (by rw [hge₁]; exact hndB) hdisj₁ hltA₁ hltB₁ hcover
  -- 距離
  have hdist₀ : (1 : Fin N) = (f₀ ^ (s.k0 + 1)) 0 := by
    have h := sameCyclePerm2_pow_pos s 0 bA e₀ bB fB hndA₀ hdisj₀ hltA₀
      hltB₀ hlenA₀ (1 + s.k0 + 0) (by omega)
      (cycleAVerts_getElem?_one s 0 bA e₀)
    rw [ofNat_zero_eq_zero, ofNat_one_eq_one hN2] at h
    rw [show s.k0 + 1 = 1 + s.k0 + 0 by omega]
    exact h.symm
  have hdist₁ : (1 : Fin N) = (f₁ ^ (s.k0 + 1 + 1)) 0 := by
    have h := sameCyclePerm2_pow_pos s 1 bA e₁ bB fB hndA₁ hdisj₁ hltA₁
      hltB₁ hlenA₁ (1 + s.k0 + 1) (by omega)
      (cycleAVerts_getElem?_one s 1 bA e₁)
    rw [ofNat_zero_eq_zero, ofNat_one_eq_one hN2] at h
    rw [show s.k0 + 1 + 1 = 1 + s.k0 + 1 by omega]
    exact h.symm
  -- 迷いAの位置
  have hstray₀ : ∀ j, (hj : j < bA.flatten.length) →
      (f₀ ^ ((s.k0 + 1) + (1 + s.k1 + j))) (0 : Fin N)
        = Fin.ofNat N (bA.flatten[j]'hj) := by
    intro j hj
    have hv : (cycleAVerts s 0 bA e₀)[2 + s.k0 + s.k1 + 0 + j]?
        = some (bA.flatten[j]'hj) := by
      rw [cycleAVerts_getElem?_stray s 0 bA e₀ j hj,
        List.getElem?_eq_getElem hj]
    have h := sameCyclePerm2_pow_pos s 0 bA e₀ bB fB hndA₀ hdisj₀ hltA₀
      hltB₀ hlenA₀ (2 + s.k0 + s.k1 + 0 + j) (by omega) hv
    rw [ofNat_zero_eq_zero] at h
    rw [show (s.k0 + 1) + (1 + s.k1 + j) = 2 + s.k0 + s.k1 + 0 + j by omega]
    exact h
  have hstray₁ : ∀ j, (hj : j < bA.flatten.length) →
      (f₁ ^ ((s.k0 + 1 + 1) + (1 + s.k1 + j))) (0 : Fin N)
        = Fin.ofNat N (bA.flatten[j]'hj) := by
    intro j hj
    have hv : (cycleAVerts s 1 bA e₁)[2 + s.k0 + s.k1 + 1 + j]?
        = some (bA.flatten[j]'hj) := by
      rw [cycleAVerts_getElem?_stray s 1 bA e₁ j hj,
        List.getElem?_eq_getElem hj]
    have h := sameCyclePerm2_pow_pos s 1 bA e₁ bB fB hndA₁ hdisj₁ hltA₁
      hltB₁ hlenA₁ (2 + s.k0 + s.k1 + 1 + j) (by omega) hv
    rw [ofNat_zero_eq_zero] at h
    rw [show (s.k0 + 1 + 1) + (1 + s.k1 + j)
      = 2 + s.k0 + s.k1 + 1 + j by omega]
    exact h
  -- 迷いBは軌道外
  have hoffB : ∀ x ∈ bB.flatten,
      (¬ f₀.SameCycle 0 (Fin.ofNat N x) ∧ ¬ f₀.SameCycle 1 (Fin.ofNat N x)) ∧
      (¬ f₁.SameCycle 0 (Fin.ofNat N x) ∧ ¬ f₁.SameCycle 1 (Fin.ofNat N x)) := by
    intro x hx
    have hxB : x ∈ cycleBVerts s c bB fB := by
      unfold cycleBVerts
      exact List.mem_append.mpr (Or.inl hx)
    have hxN : x < N := hltB x hxB
    constructor
    · refine sameCyclePerm2_offOrbit s 0 bA e₀ bB fB hndA₀ hdisj₀ hltA₀
        hltB₀ hN2 (ofNat_notMem_map hltA₀ hxN ?_)
      intro hxA
      exact hdisj₀ hxA (by rw [hge₀]; exact hxB)
    · refine sameCyclePerm2_offOrbit s 1 bA e₁ bB fB hndA₁ hdisj₁ hltA₁
        hltB₁ hN2 (ofNat_notMem_map hltA₁ hxN ?_)
      intro hxA
      exact hdisj₁ hxA (by rw [hge₁]; exact hxB)
  -- 資源
  have hresource :
      (∃ u : ℕ, s.vertexCount ≤ u ∧ u < N ∧
        (¬ f₀.SameCycle 0 (Fin.ofNat N u) ∧ ¬ f₀.SameCycle 1 (Fin.ofNat N u)) ∧
        (¬ f₁.SameCycle 0 (Fin.ofNat N u) ∧ ¬ f₁.SameCycle 1 (Fin.ofNat N u))) ∨
      (∃ w : ℕ, s.vertexCount ≤ w ∧ w < N ∧
        (f₀ ^ (ℓ - 1)) (0 : Fin N) = Fin.ofNat N w ∧
        (f₁ ^ (ℓ - 1)) (0 : Fin N) = Fin.ofNat N w) := by
    by_cases hres : s.vertexCount + c < N
    · -- 軌道外ラベル u = vc + c
      left
      refine ⟨s.vertexCount + c, by omega, hres, ?_, ?_⟩
      · refine sameCyclePerm2_offOrbit s 0 bA e₀ bB fB hndA₀ hdisj₀ hltA₀
          hltB₀ hN2 (ofNat_notMem_map hltA₀ hres ?_)
        intro hmem
        rcases mem_cycleAVerts s 0 bA e₀ hbAbd _ hmem with h | h | h | h | h
        · rcases h with h | h <;> omega
        · omega
        · rcases h with h | h <;> omega
        · omega
        · omega
      · refine sameCyclePerm2_offOrbit s 1 bA e₁ bB fB hndA₁ hdisj₁ hltA₁
          hltB₁ hN2 (ofNat_notMem_map hltA₁ hres ?_)
        intro hmem
        rcases mem_cycleAVerts s 1 bA e₁ hbAbd _ hmem with h | h | h | h | h
        · rcases h with h | h <;> omega
        · omega
        · rcases h with h | h <;> omega
        · omega
        · omega
    · -- 共通尾部ラベル w = vc + c − 1
      right
      have hc2 : 2 ≤ c := by omega
      refine ⟨s.vertexCount + c - 1, by omega, by omega, ?_, ?_⟩
      · have hv : (cycleAVerts s 0 bA e₀)[2 + s.k0 + s.k1 + 0
            + bA.flatten.length + (e₀ - 1)]?
            = some (s.vertexCount + 0 + (e₀ - 1)) :=
          cycleAVerts_getElem?_tail s 0 bA e₀ (e₀ - 1) (by omega)
        rw [show s.vertexCount + 0 + (e₀ - 1)
          = s.vertexCount + c - 1 by omega] at hv
        have h := sameCyclePerm2_pow_pos s 0 bA e₀ bB fB hndA₀ hdisj₀
          hltA₀ hltB₀ hlenA₀
          (2 + s.k0 + s.k1 + 0 + bA.flatten.length + (e₀ - 1)) (by omega) hv
        rw [ofNat_zero_eq_zero] at h
        rw [show ℓ - 1
          = 2 + s.k0 + s.k1 + 0 + bA.flatten.length + (e₀ - 1) by omega]
        exact h
      · have hv : (cycleAVerts s 1 bA e₁)[2 + s.k0 + s.k1 + 1
            + bA.flatten.length + (e₁ - 1)]?
            = some (s.vertexCount + 1 + (e₁ - 1)) :=
          cycleAVerts_getElem?_tail s 1 bA e₁ (e₁ - 1) (by omega)
        rw [show s.vertexCount + 1 + (e₁ - 1)
          = s.vertexCount + c - 1 by omega] at hv
        have h := sameCyclePerm2_pow_pos s 1 bA e₁ bB fB hndA₁ hdisj₁
          hltA₁ hltB₁ hlenA₁
          (2 + s.k0 + s.k1 + 1 + bA.flatten.length + (e₁ - 1)) (by omega) hv
        rw [ofNat_zero_eq_zero] at h
        rw [show ℓ - 1
          = 2 + s.k0 + s.k1 + 1 + bA.flatten.length + (e₁ - 1) by omega]
        exact h
  exact ⟨{
    d := s.k0 + 1
    bA := bA
    bB := bB
    f₀ := f₀
    f₁ := f₁
    hd := rfl
    cover := hcover
    hSumA := by omega
    comp₀ := comp₀
    comp₁ := comp₁
    dist₀ := hdist₀
    dist₁ := hdist₁
    strayA₀ := hstray₀
    strayA₁ := hstray₁
    offB₀ := fun x hx => (hoffB x hx).1
    offB₁ := fun x hx => (hoffB x hx).2
    resource := hresource
  }⟩

end Exists

end PeriodicTM.ClaimA

#print axioms PeriodicTM.ClaimA.exists_sameCycleData
#print axioms PeriodicTM.ClaimA.sameCyclePerm2_isCompletion
#print axioms PeriodicTM.ClaimA.sameCyclePerm2_pow_pos
#print axioms PeriodicTM.ClaimA.sameCyclePerm2_offOrbit
#print axioms PeriodicTM.ClaimA.two_bin_pack'
#print axioms PeriodicTM.ClaimA.cycleAVerts_nodup
#print axioms PeriodicTM.ClaimA.cycleBVerts_nodup
#print axioms PeriodicTM.ClaimA.cycleAB_disjoint
#print axioms PeriodicTM.ClaimA.edges_isAdj2
