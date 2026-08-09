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

end PeriodicTM.ClaimA

#print axioms PeriodicTM.ClaimA.two_bin_pack'
#print axioms PeriodicTM.ClaimA.cycleAVerts_nodup
#print axioms PeriodicTM.ClaimA.cycleBVerts_nodup
#print axioms PeriodicTM.ClaimA.cycleAB_disjoint
#print axioms PeriodicTM.ClaimA.edges_isAdj2
