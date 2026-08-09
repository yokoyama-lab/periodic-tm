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

/-- (⇒) の易しい2条件: 別軌道完成 `f` における 1 の軌道長 `m` は
`ℓ` を割り（`orbit_card_dvd`）、`m ≤ N − ℓ`（0 の軌道との非交差勘定）。
残る `k₁ + 1 ≤ m` は P₁ の頂点追跡、`q + r + 2 − ℓ ≤ m` は再パッキング
論法（f 自身では第3サイクルに迷いパスが居るかもしれないため、窓に入る
別の約数への詰め替えが要る）— いずれも後続。 -/
theorem orbit1_dvd_and_le {N ℓ : ℕ} [NeZero N] (s : AdvState)
    (f : Perm (Fin N)) (hcomp : IsCompletion N ℓ s f)
    (hdiff : ¬ f.SameCycle 0 1) :
    #{y | f.SameCycle 1 y} ∣ ℓ ∧ #{y | f.SameCycle 1 y} ≤ N - ℓ := by
  obtain ⟨hpow, hcard0, _⟩ := hcomp
  refine ⟨orbit_card_dvd f hpow 1, ?_⟩
  have hdisj := orbit_disjoint f hdiff
  have hunion :
      #(({y | f.SameCycle 0 y} : Finset (Fin N)) ∪
          ({y | f.SameCycle 1 y} : Finset (Fin N)))
        = ℓ + #{y | f.SameCycle 1 y} := by
    rw [Finset.card_union_of_disjoint hdisj, hcard0]
  have hle :
      #(({y | f.SameCycle 0 y} : Finset (Fin N)) ∪
          ({y | f.SameCycle 1 y} : Finset (Fin N))) ≤ N := by
    calc #(({y | f.SameCycle 0 y} : Finset (Fin N)) ∪
          ({y | f.SameCycle 1 y} : Finset (Fin N)))
        ≤ #(Finset.univ : Finset (Fin N)) := Finset.card_le_univ _
      _ = N := by simp
  omega

/-! ### P₁ 頂点の軌道追跡（`k₁ + 1 ≤ m` 用） -/

/-- `pathEdges` の第 `i` 辺の形。 -/
theorem pathEdges_mem {a next e i : ℕ} (hi : i < e) :
    ((if i = 0 then a else next + i - 1), next + i) ∈ pathEdges a next e :=
  List.mem_map_of_mem (List.mem_range.mpr hi)

/-- 完成 `f` がパスの辺を尊重するなら、パスの新頂点はすべて起点と同軌道。 -/
theorem sameCycle_path {N : ℕ} [NeZero N] (f : Perm (Fin N)) {a next e : ℕ}
    (hext : ∀ p ∈ pathEdges a next e,
      f (Fin.ofNat N p.1) = Fin.ofNat N p.2) :
    ∀ i, i < e → f.SameCycle (Fin.ofNat N a) (Fin.ofNat N (next + i)) := by
  intro i
  induction i with
  | zero =>
    intro h0
    have he := hext _ (pathEdges_mem (a := a) (next := next) h0)
    rw [if_pos rfl] at he
    exact ⟨1, by simpa using he⟩
  | succ i ih =>
    intro hsi
    have he := hext _ (pathEdges_mem (a := a) (next := next) hsi)
    rw [if_neg (by omega : ¬ i + 1 = 0)] at he
    have h1 : next + (i + 1) - 1 = next + i := by omega
    rw [h1] at he
    exact (ih (by omega)).trans ⟨1, by simpa using he⟩

/-- `Fin.ofNat N 1 = 1`（`N ≥ 2` のとき）。 -/
theorem ofNat_one_eq_one {N : ℕ} [NeZero N] (hN : 2 ≤ N) :
    (Fin.ofNat N 1 : Fin N) = 1 := by
  ext
  simp [Fin.ofNat, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < N)]

/-- (⇒) の第3条件: P₁ の `k₁ + 1` 頂点（`1` と新頂点 `k₁` 個）は
相異なり、すべて `1` の軌道に入る。ゆえに `k₁ + 1 ≤ m`。 -/
theorem k1_succ_le_orbit1 {N ℓ : ℕ} [NeZero N] (s : AdvState)
    (hfit : s.Fits N) (f : Perm (Fin N)) (hcomp : IsCompletion N ℓ s f) :
    s.k1 + 1 ≤ #{y | f.SameCycle 1 y} := by
  classical
  have hvc := hfit.2
  unfold AdvState.vertexCount at hvc
  have hN : 2 ≤ N := by omega
  -- P₁ の辺は s.edges に入る
  have hext1 : ∀ p ∈ pathEdges 1 (2 + s.k0) s.k1,
      f (Fin.ofNat N p.1) = Fin.ofNat N p.2 := by
    intro p hp
    exact hcomp.2.2 p (by
      unfold AdvState.edges
      exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hp))))
  -- 頂点リストとその性質
  have hlt : ∀ x ∈ (1 :: List.range' (2 + s.k0) s.k1), x < N := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · omega
    · have := (List.mem_range'_1.mp hx')
      omega
  have hnodup0 : ((1 : ℕ) :: List.range' (2 + s.k0) s.k1).Nodup := by
    refine List.nodup_cons.mpr ⟨?_, List.nodup_range'⟩
    intro hmem
    have := (List.mem_range'_1.mp hmem).1
    omega
  have hnodup : (((1 : ℕ) :: List.range' (2 + s.k0) s.k1).map
      (Fin.ofNat N)).Nodup := by
    refine List.Nodup.map_on ?_ hnodup0
    intro x hx y hy hxy
    have hxN := hlt x hx
    have hyN := hlt y hy
    have hval : x % N = y % N := by
      have := congrArg Fin.val hxy
      simpa [Fin.ofNat] using this
    rwa [Nat.mod_eq_of_lt hxN, Nat.mod_eq_of_lt hyN] at hval
  -- 全頂点が 1 の軌道に入る
  have hsub : ∀ v ∈ (((1 : ℕ) :: List.range' (2 + s.k0) s.k1).map
      (Fin.ofNat N)).toFinset, v ∈ ({y | f.SameCycle 1 y} : Finset (Fin N)) := by
    intro v hv
    simp only [List.mem_toFinset, List.mem_map] at hv
    obtain ⟨x, hx, rfl⟩ := hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases List.mem_cons.mp hx with rfl | hx'
    · rw [ofNat_one_eq_one hN]
    · obtain ⟨hx1, hx2⟩ := List.mem_range'_1.mp hx'
      have hpath := sameCycle_path f hext1 (x - (2 + s.k0)) (by omega)
      rw [show 2 + s.k0 + (x - (2 + s.k0)) = x by omega,
        ofNat_one_eq_one hN] at hpath
      exact hpath
  -- カード勘定
  calc s.k1 + 1
      = (((1 : ℕ) :: List.range' (2 + s.k0) s.k1).map
          (Fin.ofNat N)).toFinset.card := by
        rw [List.toFinset_card_of_nodup hnodup]
        simp [List.length_range']
      _ ≤ #{y | f.SameCycle 1 y} := Finset.card_le_card fun v hv => hsub v hv

/-! ## 方向別の主定理（作業中） -/

/-- 各要素が 1 以上のリストは、長さ ≤ 総和。 -/
theorem length_le_sum {l : List ℕ} (h : ∀ j ∈ l, 1 ≤ j) :
    l.length ≤ l.sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.length_cons, List.sum_cons]
    have ha := h a (List.mem_cons.mpr (Or.inl rfl))
    have ht := ih fun j hj => h j (List.mem_cons.mpr (Or.inr hj))
    omega

/-- **(⇒) の簡約**: 領域内では式側は常に成立する。`q < k₁*` は
`¬Kills`＝「窓 `[q+1, N−ℓ]` に `ℓ` の約数 `m` が存在」を与え、その
`m ≥ q+1` は `max(k₁+1, q+r+2−ℓ)` 以上（`k₁ ≤ q`、`r ≤ q ≤ ℓ−3`）。
ゆえに主張Aの (⇒) 方向は完成の存在を使わずに出る（形式化が
紙の証明より短い道を見つけた例 — 紙は 1 の軌道長を経由していた）。 -/
theorem inRegion_formulaSide {N ℓ : ℕ} (s : AdvState)
    (hfit : s.Fits N) (hreg : InLowerRegion N ℓ s) (hℓ : 3 ≤ ℓ) :
    FormulaSide N ℓ s := by
  unfold InLowerRegion at hreg
  have hq2 : s.q < ℓ - 2 := lt_of_lt_of_le hreg (min_le_left _ _)
  have hqk : s.q < PeriodicTM.TwoPointCore.k1Star N ℓ :=
    lt_of_lt_of_le hreg (min_le_right _ _)
  have hnk := PeriodicTM.TwoPointCore.not_kills_of_lt_k1Star hqk
  unfold PeriodicTM.TwoPointCore.Kills at hnk
  push_neg at hnk
  obtain ⟨m, hmℓ, hmq, hmdvd, hmN⟩ := hnk
  have hrq : s.r ≤ s.q := by
    have h1 : s.strays.length ≤ s.strays.sum := length_le_sum hfit.1
    unfold AdvState.q AdvState.r
    omega
  have hk1 : s.k1 ≤ s.q := by unfold AdvState.q; omega
  refine ⟨m, Finset.mem_range.mpr (by omega), hmdvd, ?_, hmN⟩
  exact max_le (by omega) (by omega)

/-- `k₁*` は自身が `ℓ` の約数で `N − ℓ` 以下（= `D_max`、`N > ℓ` のとき）。
¬Kills(k₁*−1) の約数証人 m ∈ [k₁*, N−ℓ] と Kills(k₁*) の
「[k₁*+1, N−ℓ] に約数なし」で m = k₁* に挟み撃つ。 -/
theorem k1Star_dvd_le {N ℓ : ℕ} (hN : ℓ < N) (hℓ : 1 ≤ ℓ) :
    PeriodicTM.TwoPointCore.k1Star N ℓ ∣ ℓ ∧
      PeriodicTM.TwoPointCore.k1Star N ℓ ≤ N - ℓ := by
  have h1 : ¬ PeriodicTM.TwoPointCore.Kills N ℓ 0 := by
    intro h
    have := h 1 (by omega) (by omega) (one_dvd ℓ)
    omega
  have hpos : 1 ≤ PeriodicTM.TwoPointCore.k1Star N ℓ := by
    rcases Nat.eq_zero_or_pos (PeriodicTM.TwoPointCore.k1Star N ℓ) with h0 | h
    · exact absurd (h0 ▸ PeriodicTM.TwoPointCore.k1Star_kills N ℓ) h1
    · exact h
  have hnk := PeriodicTM.TwoPointCore.not_kills_of_lt_k1Star
    (Nat.sub_lt hpos one_pos)
  unfold PeriodicTM.TwoPointCore.Kills at hnk
  push_neg at hnk
  obtain ⟨m, hmℓ, hm1, hdvd, hmN⟩ := hnk
  have hk := PeriodicTM.TwoPointCore.k1Star_kills N ℓ
  have hle : m ≤ PeriodicTM.TwoPointCore.k1Star N ℓ := by
    by_contra hgt
    push_neg at hgt
    have := hk m hmℓ (by omega) hdvd
    omega
  have heq : m = PeriodicTM.TwoPointCore.k1Star N ℓ := by omega
  exact ⟨heq ▸ hdvd, heq ▸ hmN⟩

/-- **2ビン貪欲詰めの十分条件**: 総和＋最大 ≤ 容量和なら、リストを
2つに分けて各側の和を容量以下にできる。証明は任意順の貪欲
（入るなら 0 側、だめなら 1 側。両方だめなら sum + max ≥ 2a > c₀+c₁
で矛盾）。(⇐) の迷いパス割当に、領域条件から出る
`V₀ + maxsize ≤ c₀ + c₁`（92,501 状態の全数検査で先に確認済み、
導出: 2Σ+k₀+k₁+4 ≤ ℓ+m）と組で使う。 -/
theorem two_bin_pack {α : Type*} (size : α → ℕ) (items : List α) :
    ∀ c0 c1 : ℕ,
      (items.map size).sum + (items.map size).foldr max 0 ≤ c0 + c1 →
      ∃ l0 l1 : List α, (l0 ++ l1).Perm items ∧
        (l0.map size).sum ≤ c0 ∧ (l1.map size).sum ≤ c1 := by
  induction items with
  | nil => exact fun c0 c1 _ => ⟨[], [], by simp, by simp, by simp⟩
  | cons a t ih =>
    intro c0 c1 h
    simp only [List.map_cons, List.sum_cons, List.foldr_cons] at h
    have hM : (t.map size).foldr max 0
        ≤ max (size a) ((t.map size).foldr max 0) := le_max_right _ _
    have hMa : size a ≤ max (size a) ((t.map size).foldr max 0) := le_max_left _ _
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

/-! ### (⇐) の構成部品: 頂点ブロックと2サイクル -/

/-- 迷いパスの頂点ブロック列: 各パス（辺数 j）は連続する j+1 頂点を占める
（埋め込み `strayEdges` と同じ開始頂点の割り振り）。 -/
def strayBlocks : ℕ → List ℕ → List (List ℕ)
  | _,    [] => []
  | next, j :: rest => List.range' next (j + 1) :: strayBlocks (next + 1 + j) rest

/-- 状態の迷いブロック（開始頂点 2 + k₀ + k₁ から）。 -/
def AdvState.blocks (s : AdvState) : List (List ℕ) :=
  strayBlocks (2 + s.k0 + s.k1) s.strays

/-- ブロックの長さは辺数 + 1。 -/
theorem strayBlocks_length_map :
    ∀ (next : ℕ) (l : List ℕ),
      (strayBlocks next l).map List.length = l.map (· + 1)
  | _, [] => rfl
  | next, j :: rest => by
    simp only [strayBlocks, List.map_cons, List.length_range',
      strayBlocks_length_map (next + 1 + j) rest]

/-- strayBlocks の全頂点は `[next, next + Σ(jᵢ+1))` に入る。 -/
theorem strayBlocks_mem_bound (l : List ℕ) :
    ∀ (next : ℕ), ∀ b ∈ strayBlocks next l, ∀ x ∈ b,
      next ≤ x ∧ x < next + (l.sum + l.length) := by
  induction l with
  | nil => intro next b hb; simp [strayBlocks] at hb
  | cons j rest ih =>
    intro next b hb x hx
    simp only [strayBlocks, List.mem_cons] at hb
    rcases hb with rfl | hb
    · have := List.mem_range'_1.mp hx
      simp only [List.sum_cons, List.length_cons]
      omega
    · have := ih (next + 1 + j) b hb x hx
      simp only [List.sum_cons, List.length_cons]
      omega

/-- 各ブロックは Nodup（連続区間だから）。 -/
theorem strayBlocks_nodup (l : List ℕ) :
    ∀ (next : ℕ), ∀ b ∈ strayBlocks next l, b.Nodup := by
  induction l with
  | nil => intro next b hb; simp [strayBlocks] at hb
  | cons j rest ih =>
    intro next b hb
    simp only [strayBlocks, List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact List.nodup_range'
    · exact ih (next + 1 + j) b hb

/-- ブロック同士は要素を共有しない（区間が前から順に切られるから）。 -/
theorem strayBlocks_pairwise (l : List ℕ) :
    ∀ (next : ℕ),
      (strayBlocks next l).Pairwise (fun b c => ∀ x ∈ b, x ∉ c) := by
  induction l with
  | nil => intro next; simp [strayBlocks]
  | cons j rest ih =>
    intro next
    refine List.Pairwise.cons ?_ (ih (next + 1 + j))
    intro c hc x hx hxc
    have h1 := List.mem_range'_1.mp hx
    have h2 := (strayBlocks_mem_bound rest (next + 1 + j) c hc x hxc).1
    omega

/-- 0 側サイクルの頂点列: `0`、P₀ の新頂点、bin0 の迷いブロック、
未開示点での充填（長さ ℓ に合わせる）。 -/
def cycle0Verts (s : AdvState) (b0 : List (List ℕ)) (fill0 : List ℕ) : List ℕ :=
  (0 :: List.range' 2 s.k0) ++ b0.flatten ++ fill0

/-- 1 側サイクルの頂点列: `1`、P₁ の新頂点、bin1 の迷いブロック、充填。 -/
def cycle1Verts (s : AdvState) (b1 : List (List ℕ)) (fill1 : List ℕ) : List ℕ :=
  (1 :: List.range' (2 + s.k0) s.k1) ++ b1.flatten ++ fill1

/-- b が状態のブロック由来なら、その頂点は `[2+k₀+k₁, vertexCount)`。 -/
theorem blocks_mem_bound (s : AdvState) {b : List ℕ} (hb : b ∈ s.blocks)
    {x : ℕ} (hx : x ∈ b) :
    2 + s.k0 + s.k1 ≤ x ∧ x < s.vertexCount := by
  have := strayBlocks_mem_bound s.strays (2 + s.k0 + s.k1) b hb x hx
  unfold AdvState.vertexCount
  omega

/-- サイクル 0 の頂点列は Nodup: 部品の値域が
`{0} ∪ [2, 2+k₀)` ／ `[2+k₀+k₁, vc)` ／ `[vc, ·)` と階層化されるから。 -/
theorem cycle0Verts_nodup (s : AdvState) (b0 : List (List ℕ)) (fill0 : List ℕ)
    (hbmem : ∀ b ∈ b0, b ∈ s.blocks) (hbnd : b0.Pairwise List.Disjoint)
    (hbdup : ∀ b ∈ b0, b.Nodup)
    (hfnd : fill0.Nodup) (hflo : ∀ x ∈ fill0, s.vertexCount ≤ x) :
    (cycle0Verts s b0 fill0).Nodup := by
  have hbx : ∀ b ∈ b0, ∀ x ∈ b, 2 + s.k0 + s.k1 ≤ x ∧ x < s.vertexCount :=
    fun b hb x hx => blocks_mem_bound s (hbmem b hb) hx
  have hflat : ∀ x ∈ b0.flatten, 2 + s.k0 + s.k1 ≤ x ∧ x < s.vertexCount := by
    intro x hx
    obtain ⟨b, hb, hxb⟩ := List.mem_flatten.mp hx
    exact hbx b hb x hxb
  unfold cycle0Verts
  rw [List.cons_append]
  refine List.nodup_cons.mpr ⟨?_, ?_⟩
  · intro h
    rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · have := (List.mem_range'_1.mp h).1
        omega
      · have := (hflat 0 h).1
        omega
    · have h1 := hflo 0 h
      have h2 : 2 ≤ s.vertexCount := by unfold AdvState.vertexCount; omega
      omega
  · refine List.Nodup.append
      (List.Nodup.append List.nodup_range'
        (List.nodup_flatten.mpr ⟨hbdup, hbnd⟩) ?_) hfnd ?_
    · intro x hx hx'
      have h1 := List.mem_range'_1.mp hx
      have h2 := (hflat x hx').1
      omega
    · intro x hx hx'
      have h2 := hflo x hx'
      rcases List.mem_append.mp hx with h | h
      · have h1 := List.mem_range'_1.mp h
        have h3 : 2 + s.k0 ≤ s.vertexCount := by
          unfold AdvState.vertexCount; omega
        omega
      · have := (hflat x h).2
        omega

/-- サイクル 1 の頂点列は Nodup（cycle0 と同型。頭部の値域は
`{1} ∪ [2+k₀, 2+k₀+k₁)`）。 -/
theorem cycle1Verts_nodup (s : AdvState) (b1 : List (List ℕ)) (fill1 : List ℕ)
    (hbmem : ∀ b ∈ b1, b ∈ s.blocks) (hbnd : b1.Pairwise List.Disjoint)
    (hbdup : ∀ b ∈ b1, b.Nodup)
    (hfnd : fill1.Nodup) (hflo : ∀ x ∈ fill1, s.vertexCount ≤ x) :
    (cycle1Verts s b1 fill1).Nodup := by
  have hflat : ∀ x ∈ b1.flatten, 2 + s.k0 + s.k1 ≤ x ∧ x < s.vertexCount := by
    intro x hx
    obtain ⟨b, hb, hxb⟩ := List.mem_flatten.mp hx
    exact blocks_mem_bound s (hbmem b hb) hxb
  unfold cycle1Verts
  rw [List.cons_append]
  refine List.nodup_cons.mpr ⟨?_, ?_⟩
  · intro h
    rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · have := (List.mem_range'_1.mp h).1
        omega
      · have := (hflat 1 h).1
        omega
    · have h1 := hflo 1 h
      have h2 : 2 ≤ s.vertexCount := by unfold AdvState.vertexCount; omega
      omega
  · refine List.Nodup.append
      (List.Nodup.append List.nodup_range'
        (List.nodup_flatten.mpr ⟨hbdup, hbnd⟩) ?_) hfnd ?_
    · intro x hx hx'
      have h1 := List.mem_range'_1.mp hx
      have h2 := (hflat x hx').1
      omega
    · intro x hx hx'
      have h2 := hflo x hx'
      rcases List.mem_append.mp hx with h | h
      · have h1 := List.mem_range'_1.mp h
        have h3 : 2 + s.k0 + s.k1 ≤ s.vertexCount := by
          unfold AdvState.vertexCount; omega
        omega
      · have := (hflat x h).2
        omega

/-- サイクル 0 の頂点の所属は3つの帯に分かれる（頭部・ブロック・充填）。 -/
theorem mem_cycle0Verts (s : AdvState) (b0 : List (List ℕ)) (fill0 : List ℕ)
    (hb0 : ∀ b ∈ b0, ∀ x ∈ b, 2 + s.k0 + s.k1 ≤ x ∧ x < s.vertexCount)
    (hf0 : ∀ x ∈ fill0, s.vertexCount ≤ x) :
    ∀ x ∈ cycle0Verts s b0 fill0,
      (x < 2 + s.k0 ∧ x ≠ 1) ∨
      (2 + s.k0 + s.k1 ≤ x ∧ x < s.vertexCount ∧ ∃ b ∈ b0, x ∈ b) ∨
      (s.vertexCount ≤ x ∧ x ∈ fill0) := by
  intro x hx
  unfold cycle0Verts at hx
  rcases List.mem_append.mp hx with h | h
  · rcases List.mem_append.mp h with h | h
    · rcases List.mem_cons.mp h with rfl | h
      · exact Or.inl ⟨by omega, by omega⟩
      · have := List.mem_range'_1.mp h
        exact Or.inl ⟨by omega, by omega⟩
    · obtain ⟨b, hb, hxb⟩ := List.mem_flatten.mp h
      have := hb0 b hb x hxb
      exact Or.inr (Or.inl ⟨this.1, this.2, b, hb, hxb⟩)
  · exact Or.inr (Or.inr ⟨hf0 x h, h⟩)

/-- サイクル 1 の頂点の所属（頭部の帯は `{1} ∪ [2+k₀, 2+k₀+k₁)`）。 -/
theorem mem_cycle1Verts (s : AdvState) (b1 : List (List ℕ)) (fill1 : List ℕ)
    (hb1 : ∀ b ∈ b1, ∀ x ∈ b, 2 + s.k0 + s.k1 ≤ x ∧ x < s.vertexCount)
    (hf1 : ∀ x ∈ fill1, s.vertexCount ≤ x) :
    ∀ x ∈ cycle1Verts s b1 fill1,
      (x = 1 ∨ (2 + s.k0 ≤ x ∧ x < 2 + s.k0 + s.k1)) ∨
      (2 + s.k0 + s.k1 ≤ x ∧ x < s.vertexCount ∧ ∃ b ∈ b1, x ∈ b) ∨
      (s.vertexCount ≤ x ∧ x ∈ fill1) := by
  intro x hx
  unfold cycle1Verts at hx
  rcases List.mem_append.mp hx with h | h
  · rcases List.mem_append.mp h with h | h
    · rcases List.mem_cons.mp h with rfl | h
      · exact Or.inl (Or.inl rfl)
      · have := List.mem_range'_1.mp h
        exact Or.inl (Or.inr ⟨by omega, by omega⟩)
    · obtain ⟨b, hb, hxb⟩ := List.mem_flatten.mp h
      have := hb1 b hb x hxb
      exact Or.inr (Or.inl ⟨this.1, this.2, b, hb, hxb⟩)
  · exact Or.inr (Or.inr ⟨hf1 x h, h⟩)

/-- **2つのサイクルは頂点を共有しない。** 頭部の帯は数値的に分離
（`{0} ∪ [2,2+k₀)` と `{1} ∪ [2+k₀,2+k₀+k₁)`）、ブロック同士は
`two_bin_pack` の分割（`hcross`）、充填同士は仮定 `hfd` による。 -/
theorem cycles_disjoint (s : AdvState) (b0 b1 : List (List ℕ))
    (fill0 fill1 : List ℕ)
    (hb0 : ∀ b ∈ b0, ∀ x ∈ b, 2 + s.k0 + s.k1 ≤ x ∧ x < s.vertexCount)
    (hb1 : ∀ b ∈ b1, ∀ x ∈ b, 2 + s.k0 + s.k1 ≤ x ∧ x < s.vertexCount)
    (hcross : ∀ b ∈ b0, ∀ c ∈ b1, ∀ x ∈ b, x ∉ c)
    (hf0 : ∀ x ∈ fill0, s.vertexCount ≤ x)
    (hf1 : ∀ x ∈ fill1, s.vertexCount ≤ x)
    (hfd : List.Disjoint fill0 fill1) :
    List.Disjoint (cycle0Verts s b0 fill0) (cycle1Verts s b1 fill1) := by
  have hvc : 2 + s.k0 + s.k1 ≤ s.vertexCount := by
    unfold AdvState.vertexCount; omega
  intro x hx hx'
  rcases mem_cycle0Verts s b0 fill0 hb0 hf0 x hx with h0 | h0 | h0 <;>
    rcases mem_cycle1Verts s b1 fill1 hb1 hf1 x hx' with h1 | h1 | h1
  · rcases h1 with rfl | h1
    · exact h0.2 rfl
    · omega
  · omega
  · omega
  · rcases h1 with rfl | h1 <;> omega
  · obtain ⟨_, _, b, hb, hxb⟩ := h0
    obtain ⟨_, _, c, hc, hxc⟩ := h1
    exact hcross b hb c hc x hxb hxc
  · omega
  · rcases h1 with rfl | h1 <;> omega
  · omega
  · exact hfd h0.2 h1.2

/-- (⇐) の完成の構成: 2 つのサイクルの `formPerm` の積。
`b0 ++ b1` は `s.blocks` の置換（`two_bin_pack` の出力）、
`fill0 ++ fill1` は未開示点 `[vertexCount, N)` の分割。
正しさ（`IsCompletion`・別軌道）の検証はこの後の作業。 -/
def buildPerm (N : ℕ) [NeZero N] (s : AdvState)
    (b0 b1 : List (List ℕ)) (fill0 fill1 : List ℕ) : Perm (Fin N) :=
  ((cycle0Verts s b0 fill0).map (Fin.ofNat N)).formPerm *
    ((cycle1Verts s b1 fill1).map (Fin.ofNat N)).formPerm

/-! ### formPerm の代数的性質（位数条件 `f ^ ℓ = 1` 用）

サイクル長がそれぞれ `ℓ` と `m ∣ ℓ` なので、互いに素な 2 つの
`formPerm` の積は `ℓ` 乗で単位元になる。ここは一般の `α` で示す。 -/

section FormPerm

variable {α : Type*} [DecidableEq α]

/-- リスト長が `n` を割るなら `formPerm l ^ n = 1`（`l` は Nodup）。
1 のサイクル（長さ `m ∣ ℓ`）を `ℓ` 乗で消すのに使う。 -/
theorem formPerm_pow_eq_one_of_dvd {l : List α} (hl : l.Nodup) {n : ℕ}
    (hd : l.length ∣ n) : l.formPerm ^ n = 1 := by
  obtain ⟨k, rfl⟩ := hd
  -- 注: mathlib 側の `l` は明示引数（Perm/List.lean の `variable (l)`）
  rw [pow_mul, List.formPerm_pow_length_eq_one_of_nodup _ hl, one_pow]

/-- 頂点を共有しないリストの `formPerm` は（置換として）互いに素。
台の外は動かさないことから直接出る。 -/
theorem formPerm_disjoint {l₁ l₂ : List α} (h : List.Disjoint l₁ l₂) :
    Perm.Disjoint l₁.formPerm l₂.formPerm := by
  intro x
  by_cases hx : x ∈ l₁
  · exact Or.inr (List.formPerm_apply_of_notMem (h hx))
  · exact Or.inl (List.formPerm_apply_of_notMem hx)

/-- **位数条件の一般形**: 互いに素な 2 つの Nodup リストの `formPerm` の
積は、両方の長さが `n` を割るとき `n` 乗で単位元。 -/
theorem formPerm_mul_pow_eq_one {l₁ l₂ : List α} (h₁ : l₁.Nodup) (h₂ : l₂.Nodup)
    (hd : List.Disjoint l₁ l₂) {n : ℕ}
    (hn₁ : l₁.length ∣ n) (hn₂ : l₂.length ∣ n) :
    (l₁.formPerm * l₂.formPerm) ^ n = 1 := by
  rw [(formPerm_disjoint hd).commute.mul_pow,
    formPerm_pow_eq_one_of_dvd h₁ hn₁, formPerm_pow_eq_one_of_dvd h₂ hn₂, one_mul]

/-- `formPerm` の反復はリストの外へ出ない。 -/
theorem formPerm_pow_mem {l : List α} {x : α} (hx : x ∈ l) :
    ∀ k : ℕ, (l.formPerm ^ k) x ∈ l := by
  intro k
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [pow_succ', Perm.mul_apply]
    exact List.formPerm_apply_mem_of_mem ih

/-- **積の作用は自分のサイクル上では片側だけ**: `l₁` の点では
`l₂` の `formPerm` は恒等なので、積の反復は `l₁` 側の反復に一致する。
「0 の軌道が `l₁` に閉じている」ことの土台。 -/
theorem mul_pow_apply_of_mem {l₁ l₂ : List α} (hd : List.Disjoint l₁ l₂) :
    ∀ (k : ℕ) {x : α}, x ∈ l₁ →
      ((l₁.formPerm * l₂.formPerm) ^ k) x = (l₁.formPerm ^ k) x := by
  intro k
  induction k with
  | zero => intro x _; simp
  | succ k ih =>
    intro x hx
    rw [pow_succ, pow_succ, Perm.mul_apply, Perm.mul_apply, Perm.mul_apply,
      List.formPerm_apply_of_notMem (hd hx)]
    exact ih (List.formPerm_apply_mem_of_mem hx)

/-- 同じ Nodup リスト上の 2 点は**自然数**歩で到達できる
（`i` から `j` へは `j + (len − i)` 歩。mod を避ける歩数の取り方）。 -/
theorem formPerm_exists_pow {l : List α} (hl : l.Nodup) {x y : α}
    (hx : x ∈ l) (hy : y ∈ l) : ∃ k : ℕ, (l.formPerm ^ k) x = y := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
  refine ⟨j + (l.length - i), ?_⟩
  rw [List.formPerm_pow_apply_getElem l hl]
  have hidx : (i + (j + (l.length - i))) % l.length = j := by
    have h : i + (j + (l.length - i)) = j + l.length := by omega
    rw [h, Nat.add_mod_right, Nat.mod_eq_of_lt hj]
  simp [hidx]

/-- 同じ Nodup リスト上の 2 点は `formPerm` の同一軌道にある。 -/
theorem formPerm_sameCycle {l : List α} (hl : l.Nodup) {x y : α}
    (hx : x ∈ l) (hy : y ∈ l) : Perm.SameCycle l.formPerm x y := by
  obtain ⟨k, hk⟩ := formPerm_exists_pow hl hx hy
  exact ⟨(k : ℤ), by rw [zpow_natCast]; exact hk⟩

/-- **軌道は自分のサイクルに閉じている**: `l₁` の点から積で到達できる
点は `l₁` の中だけ。有限性で `zpow` を `npow` に落として
`mul_pow_apply_of_mem` と `formPerm_pow_mem` を使う。 -/
theorem sameCycle_mem_of_mem [Finite α] {l₁ l₂ : List α}
    (hd : List.Disjoint l₁ l₂) {x y : α} (hx : x ∈ l₁)
    (h : Perm.SameCycle (l₁.formPerm * l₂.formPerm) x y) : y ∈ l₁ := by
  obtain ⟨i, _, rfl⟩ := h.exists_pow_eq'
  rw [mul_pow_apply_of_mem hd i hx]
  exact formPerm_pow_mem hx i

end FormPerm

/-! ### 軌道の同定（`IsCompletion` の「軌道長 = ℓ」と「別軌道」） -/

/-- **軌道 = 自分のサイクルのリスト**（Finset として）。 -/
theorem orbit_eq_toFinset {N : ℕ} {l₁ l₂ : List (Fin N)} (hl : l₁.Nodup)
    (hd : List.Disjoint l₁ l₂) {x : Fin N} (hx : x ∈ l₁) :
    ({y | (l₁.formPerm * l₂.formPerm).SameCycle x y} : Finset (Fin N))
      = l₁.toFinset := by
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset]
  constructor
  · exact fun h => sameCycle_mem_of_mem hd hx h
  · intro hy
    obtain ⟨k, hk⟩ := formPerm_exists_pow hl hx hy
    exact ⟨(k : ℤ), by rw [zpow_natCast, mul_pow_apply_of_mem hd k hx]; exact hk⟩

/-- **軌道長 = リスト長**（`Valid` の `#{y | SameCycle 0 y} = ℓ` の形）。 -/
theorem orbit_card {N : ℕ} {l₁ l₂ : List (Fin N)} (hl : l₁.Nodup)
    (hd : List.Disjoint l₁ l₂) {x : Fin N} (hx : x ∈ l₁) :
    #{y | (l₁.formPerm * l₂.formPerm).SameCycle x y} = l₁.length := by
  rw [orbit_eq_toFinset hl hd hx, List.toFinset_card_of_nodup hl]

/-- **0 と 1 は別軌道**: `1` は `l₁` の外にあるので、`l₁` に閉じた
軌道からは届かない。 -/
theorem not_sameCycle_of_notMem {N : ℕ} {l₁ l₂ : List (Fin N)}
    (hd : List.Disjoint l₁ l₂) {x y : Fin N} (hx : x ∈ l₁) (hy : y ∉ l₁) :
    ¬ (l₁.formPerm * l₂.formPerm).SameCycle x y :=
  fun h => hy (sameCycle_mem_of_mem hd hx h)

/-- `Fin.ofNat N` は `[0, N)` 上で単射（構成リストの Nodup を
`Fin N` へ移すのに使う）。 -/
theorem ofNat_injOn {N : ℕ} [NeZero N] {l : List ℕ} (hl : ∀ x ∈ l, x < N)
    (hnd : l.Nodup) : (l.map (Fin.ofNat N)).Nodup := by
  refine List.Nodup.map_on ?_ hnd
  intro x hx y hy hxy
  have hval : x % N = y % N := by
    have := congrArg Fin.val hxy
    simpa [Fin.ofNat] using this
  rwa [Nat.mod_eq_of_lt (hl x hx), Nat.mod_eq_of_lt (hl y hy)] at hval

/-- `List.Disjoint` は `Fin.ofNat` の像でも保たれる（`[0, N)` 上）。 -/
theorem ofNat_disjoint {N : ℕ} [NeZero N] {l₁ l₂ : List ℕ}
    (h₁ : ∀ x ∈ l₁, x < N) (h₂ : ∀ x ∈ l₂, x < N) (hd : List.Disjoint l₁ l₂) :
    List.Disjoint (l₁.map (Fin.ofNat N)) (l₂.map (Fin.ofNat N)) := by
  intro z hz hz'
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
  obtain ⟨y, hy, hxy⟩ := List.mem_map.mp hz'
  have hval : y % N = x % N := by
    have := congrArg Fin.val hxy
    simpa [Fin.ofNat] using this
  rw [Nat.mod_eq_of_lt (h₁ x hx), Nat.mod_eq_of_lt (h₂ y hy)] at hval
  exact hd hx (hval ▸ hy)

/-- (⇒) 必要性（系）: 領域内なら完成の存在に依らず式側が成立。 -/
theorem completion_to_formula {N ℓ : ℕ} [NeZero N] (s : AdvState)
    (hfit : s.Fits N) (hreg : InLowerRegion N ℓ s) (hℓ : 3 ≤ ℓ)
    (_h : CompletionSide N ℓ s) : FormulaSide N ℓ s :=
  inRegion_formulaSide s hfit hreg hℓ

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
