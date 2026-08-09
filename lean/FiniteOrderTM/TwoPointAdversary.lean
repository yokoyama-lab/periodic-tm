/-
FiniteOrderTM/TwoPointAdversary.lean
— 新鮮応答敵対者の状態遷移（定理9.6 の下界、roadmap ステップ5 の土台）

決定木を1手進めるたびに `AdvState` がどう変わるかを定義し、下界の
帰納が必要とする**単調性**だけを取り出す:
  1手で `q` は高々 +1、頂点数は高々 +2。
これにより「深さ `q` の木では常に `s.q ≤ q`」が言え、
`InLowerRegion` の維持（＝別軌道完成の生存、`ClaimA.completion_survives`）と
`survives_two_distances` が各段で使える。

**BUILD NOTE**: root（`FiniteOrderTM.lean`）非取込。検査は
`lake env lean FiniteOrderTM/TwoPointAdversary.lean`。
-/
import FiniteOrderTM.TwoPointClaimAGeneral
import FiniteOrderTM.QueryGame
import FiniteOrderTM.TwoPointBridge

namespace PeriodicTM.ClaimA

open Equiv Finset

/-! ### リストの1点更新（`strays` の第 i 本を伸ばす） -/

/-- 第 `i` 要素を 1 増やすと総和も 1 増える（`i` が範囲内のとき）。
mathlib に `List.sum_set` が無いので用意する。 -/
theorem sum_set_succ : ∀ (l : List ℕ) (i : ℕ), i < l.length →
    (l.set i (l[i]?.getD 0 + 1)).sum = l.sum + 1
  | [], _, h => absurd h (by simp)
  | a :: t, 0, _ => by simp; omega
  | a :: t, i + 1, h => by
    have ht : i < t.length := by simpa using h
    simp only [List.set_cons_succ, List.sum_cons, List.getElem?_cons_succ,
      sum_set_succ t i ht]
    omega

/-! ### クエリの分類と状態遷移

新鮮応答敵対者は、開示済みパスの末端が問われたらそのパスを伸ばし、
未開示点が問われたら新しい迷いパスを作る。既に答えの決まっている点
（内部点）を問われても情報は増えない。 -/

/-- 1手のクエリの種類。 -/
inductive QueryKind where
  | extendP0
  | extendP1
  | extendStray (i : ℕ)
  | fresh
  | stale
deriving DecidableEq

/-- 1手進めた状態。 -/
def AdvState.step (s : AdvState) : QueryKind → AdvState
  | .extendP0 => ⟨s.k0 + 1, s.k1, s.strays⟩
  | .extendP1 => ⟨s.k0, s.k1 + 1, s.strays⟩
  | .extendStray i => ⟨s.k0, s.k1, s.strays.set i (s.strays[i]?.getD 0 + 1)⟩
  | .fresh => ⟨s.k0, s.k1, 1 :: s.strays⟩
  | .stale => s

/-- **1手で `q` は高々 +1**。 -/
theorem AdvState.step_q_le (s : AdvState) (k : QueryKind) :
    (s.step k).q ≤ s.q + 1 := by
  cases k with
  | extendP0 => simp only [AdvState.step, AdvState.q]; omega
  | extendP1 => simp only [AdvState.step, AdvState.q]; omega
  | extendStray i =>
    by_cases hi : i < s.strays.length
    · have h := sum_set_succ s.strays i hi
      simp only [AdvState.step, AdvState.q]
      omega
    · have hle : s.strays.length ≤ i := by omega
      simp only [AdvState.step, AdvState.q, List.set_eq_of_length_le hle]
      omega
  | fresh => simp only [AdvState.step, AdvState.q, List.sum_cons]; omega
  | stale => simp only [AdvState.step]; omega

/-- **1手で頂点数は高々 +2**（新しい迷いパスは頂点2つを使う）。 -/
theorem AdvState.step_vertexCount_le (s : AdvState) (k : QueryKind) :
    (s.step k).vertexCount ≤ s.vertexCount + 2 := by
  cases k with
  | extendP0 => simp only [AdvState.step, AdvState.vertexCount]; omega
  | extendP1 => simp only [AdvState.step, AdvState.vertexCount]; omega
  | extendStray i =>
    by_cases hi : i < s.strays.length
    · have h := sum_set_succ s.strays i hi
      simp only [AdvState.step, AdvState.vertexCount, List.length_set]
      omega
    · have hle : s.strays.length ≤ i := by omega
      simp only [AdvState.step, AdvState.vertexCount,
        List.set_eq_of_length_le hle]
      omega
  | fresh =>
    simp only [AdvState.step, AdvState.vertexCount, List.sum_cons,
      List.length_cons]
    omega
  | stale => simp only [AdvState.step]; omega

/-- 迷いパスの正値性（`Fits` の第1条件）は遷移で保たれる。 -/
theorem AdvState.step_strays_pos (s : AdvState) (k : QueryKind)
    (h : ∀ j ∈ s.strays, 1 ≤ j) : ∀ j ∈ (s.step k).strays, 1 ≤ j := by
  cases k with
  | extendP0 => exact h
  | extendP1 => exact h
  | extendStray i =>
    intro j hj
    rcases List.mem_or_eq_of_mem_set hj with hj' | hj'
    · exact h j hj'
    · omega
  | fresh =>
    intro j hj
    rcases List.mem_cons.mp hj with rfl | hj'
    · omega
    · exact h j hj'
  | stale => exact h

/-- **多手版**: `n` 手進めても `q ≤ 初期 q + n`。深さ `q` の木に対し
`s.q ≤ q` を与える（下界の帰納の骨）。 -/
theorem AdvState.steps_q_le (s : AdvState) :
    ∀ (ks : List QueryKind), (ks.foldl AdvState.step s).q ≤ s.q + ks.length := by
  intro ks
  induction ks generalizing s with
  | nil => simp
  | cons k t ih =>
    have h1 := ih (s.step k)
    have h2 := s.step_q_le k
    simp only [List.foldl_cons, List.length_cons]
    omega

/-! ### 決定木に沿った対局

敵対者の戦略は「問われた点にどう答えるか（どの枝へ行くか）」と
「状態をどう更新するか」の組。**下界の予算勘定はどんな戦略でも成り立つ**
ので、ここでは戦略を抽象的に受け取る（新鮮応答が具体例）。 -/

/-- 敵対者の戦略: 答え（枝の選択）と状態更新の種類。 -/
structure Strategy (N : ℕ) where
  answer : AdvState → Fin N → Fin N
  kind : AdvState → Fin N → QueryKind

/-- 木を戦略に沿って最後まで辿ったときの終状態。 -/
def play {N : ℕ} (σ : Strategy N) :
    {q : ℕ} → PeriodicTM.QueryGame.Tree N q → AdvState → AdvState
  | _, .leaf _ _, s => s
  | _, .node x child, s =>
      play σ (child (σ.answer s x)) (s.step (σ.kind s x))

/-- **予算勘定**: 深さ `q` の木を辿っても `q` は高々 `q` しか増えない。
どんな戦略でも成り立つ（各手が `step` 1回だから）。 -/
theorem play_q_le {N : ℕ} (σ : Strategy N) :
    ∀ {q : ℕ} (t : PeriodicTM.QueryGame.Tree N q) (s : AdvState),
      (play σ t s).q ≤ s.q + q
  | _, .leaf _ _, s => by simp [play]
  | _, .node x child, s => by
    have h1 := play_q_le σ (child (σ.answer s x)) (s.step (σ.kind s x))
    have h2 := s.step_q_le (σ.kind s x)
    simp only [play]
    omega

/-- **領域内に留まる**: 深さが `min (ℓ−2) (k₁*)` 未満の木では、
終状態も下界領域にいる（初期状態が `q = 0` のとき）。
これと `ClaimA.completion_survives` で「別軌道完成は最後まで生存」、
`TwoPointBridge.survives_two_distances` で「型3以外の出力は死ぬ」。 -/
theorem play_inLowerRegion {N ℓ : ℕ} (σ : Strategy N) {q : ℕ}
    (t : PeriodicTM.QueryGame.Tree N q) (s : AdvState) (hs : s.q = 0)
    (hq : q < min (ℓ - 2) (PeriodicTM.TwoPointCore.k1Star N ℓ)) :
    InLowerRegion N ℓ (play σ t s) := by
  have := play_q_le σ t s
  unfold InLowerRegion
  omega

/-! ### 開示頂点の分類（葉の出力対を4型へ写す規則）

埋め込みの頂点番号は `0`・`1`・P₀ の新頂点 `[2, 2+k₀)`・P₁ の新頂点
`[2+k₀, 2+k₀+k₁)`・迷い頂点・未開示点。前4者は `0` または `1` からの
オフセットが確定しているので、出力対の型（research/09 の表）が決まる。 -/

/-- 開示頂点の所属。`onP0 a` は「`f^a(0)` である」の意。 -/
inductive VertexClass where
  | onP0 (a : ℕ)
  | onP1 (a : ℕ)
  | other
deriving DecidableEq

/-- 頂点番号から所属を読む（番号付けは `AdvState.edges` の埋め込みと同じ）。 -/
def AdvState.classify (s : AdvState) (v : ℕ) : VertexClass :=
  if v = 0 then .onP0 0
  else if v = 1 then .onP1 0
  else if 2 ≤ v ∧ v < 2 + s.k0 then .onP0 (v - 1)
  else if 2 + s.k0 ≤ v ∧ v < 2 + s.k0 + s.k1 then .onP1 (v - 1 - s.k0)
  else .other

/-- 出力対の型（両成分とも所属が確定しているときだけ定まる）。
`none` は「未開示点か迷い点を含む出力」で、敵対者は軌道外配置で殺す。 -/
def AdvState.outputType (s : AdvState) (ℓ : ℕ) (v₀ v₁ : ℕ) :
    Option (PeriodicTM.TwoPointBridge.OutputType ℓ) :=
  match s.classify v₀, s.classify v₁ with
  | .onP0 a, .onP0 b => some (.type1 (a : ZMod ℓ) (b : ZMod ℓ))
  | .onP0 a, .onP1 b => some (.type2 (a : ZMod ℓ) (b : ZMod ℓ))
  | .onP1 a, .onP0 b => some (.type3 (a : ZMod ℓ) (b : ZMod ℓ))
  | .onP1 a, .onP1 b => some (.type4 (a : ZMod ℓ) (b : ZMod ℓ))
  | _, _ => none

/-! ### 分類が正しいこと（完成のもとで位置が一致する） -/

/-- P₀ の辺は状態の辺集合に含まれる。 -/
theorem mem_edges_P0 {s : AdvState} {p : ℕ × ℕ}
    (hp : p ∈ pathEdges 0 2 s.k0) : p ∈ s.edges := by
  unfold AdvState.edges
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hp)))

/-- **P₀ 上の位置は宣言どおり**: 任意の完成 `f` で、`0` から `a+1` 歩
進んだ点は頂点番号 `2 + a`（`a < k₀`）。すなわち `classify` が
`onP0 (a+1)` と読む頂点は本当に `f^(a+1)(0)` である。 -/
theorem completion_pow_zero {N ℓ : ℕ} [NeZero N] (s : AdvState)
    (f : Perm (Fin N)) (hcomp : IsCompletion N ℓ s f) :
    ∀ a, a < s.k0 → (f ^ (a + 1)) (Fin.ofNat N 0) = Fin.ofNat N (2 + a) := by
  intro a
  induction a with
  | zero =>
    intro h
    have he := hcomp.2.2 _ (mem_edges_P0 (pathEdges_mem (a := 0) (next := 2) h))
    rw [if_pos rfl] at he
    simpa using he
  | succ a ih =>
    intro h
    have hprev := ih (by omega)
    have he := hcomp.2.2 _
      (mem_edges_P0 (pathEdges_mem (a := 0) (next := 2) h))
    rw [if_neg (by omega : ¬ a + 1 = 0)] at he
    have hidx : 2 + (a + 1) - 1 = 2 + a := by omega
    rw [hidx] at he
    rw [pow_succ', Perm.mul_apply, hprev, he]

/-- P₁ の辺も状態の辺集合に含まれる。 -/
theorem mem_edges_P1 {s : AdvState} {p : ℕ × ℕ}
    (hp : p ∈ pathEdges 1 (2 + s.k0) s.k1) : p ∈ s.edges := by
  unfold AdvState.edges
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hp)))

/-- **P₁ 上の位置は宣言どおり**: 任意の完成で `1` から `a+1` 歩進んだ点は
頂点番号 `2 + k₀ + a`（`a < k₁`）。 -/
theorem completion_pow_one {N ℓ : ℕ} [NeZero N] (s : AdvState)
    (f : Perm (Fin N)) (hcomp : IsCompletion N ℓ s f) :
    ∀ a, a < s.k1 →
      (f ^ (a + 1)) (Fin.ofNat N 1) = Fin.ofNat N (2 + s.k0 + a) := by
  intro a
  induction a with
  | zero =>
    intro h
    have he := hcomp.2.2 _
      (mem_edges_P1 (pathEdges_mem (a := 1) (next := 2 + s.k0) h))
    rw [if_pos rfl] at he
    simpa using he
  | succ a ih =>
    intro h
    have hprev := ih (by omega)
    have he := hcomp.2.2 _
      (mem_edges_P1 (pathEdges_mem (a := 1) (next := 2 + s.k0) h))
    rw [if_neg (by omega : ¬ a + 1 = 0)] at he
    have hidx : 2 + s.k0 + (a + 1) - 1 = 2 + s.k0 + a := by omega
    rw [hidx] at he
    rw [pow_succ', Perm.mul_apply, hprev, he]

/-- **同一軌道完成での P₁ 側の絶対位置**: `1 = f^d(0)` なら、
`classify` が `onP1 (a+1)` と読む頂点の位置は `d + (a+1)`。
これは補題9.4 の型3・型4 の `d + α` の形そのもの。 -/
theorem completion_onP1_pos {N ℓ : ℕ} [NeZero N] (s : AdvState)
    (f : Perm (Fin N)) (hcomp : IsCompletion N ℓ s f) {d : ℕ}
    (hd : Fin.ofNat N 1 = (f ^ d) (Fin.ofNat N 0)) :
    ∀ a, a < s.k1 →
      (f ^ ((a + 1) + d)) (Fin.ofNat N 0) = Fin.ofNat N (2 + s.k0 + a) := by
  intro a ha
  rw [pow_add, Perm.mul_apply, ← hd]
  exact completion_pow_one s f hcomp a ha

/-! ### 葉での kill（別軌道完成による型3の撃墜）

`GoodOutput` の反射は軌道を保つので、出力の第1成分は必ず `0` と
同一軌道でなければならない。別軌道完成では `1` 側の点はこれを満たさず、
**型3（`v₀` が `1` 側）は問答無用で死ぬ**。研究ノート09 の
「型3は別軌道完成で殺す」の具体形。 -/

/-- `GoodOutput` なら第1成分は `a` と同一軌道（反射が軌道を保つから）。 -/
theorem goodOutput_sameCycle_left {N : ℕ} {f : Perm (Fin N)}
    {a b v₀ v₁ : Fin N}
    (h : PeriodicTM.QueryGame.GoodOutput a b f v₀ v₁) : f.SameCycle a v₀ := by
  obtain ⟨ι, ⟨_, horb, _⟩, ha, _⟩ := h
  rw [← ha]
  exact horb a

/-- 同様に第2成分は `b` と同一軌道。 -/
theorem goodOutput_sameCycle_right {N : ℕ} {f : Perm (Fin N)}
    {a b v₀ v₁ : Fin N}
    (h : PeriodicTM.QueryGame.GoodOutput a b f v₀ v₁) : f.SameCycle b v₁ := by
  obtain ⟨ι, ⟨_, horb, _⟩, _, hb⟩ := h
  rw [← hb]
  exact horb b

/-- **別軌道完成による撃墜**: `0` と `1` が別軌道なら、`1` 側の点を
第1成分に出す対（＝型3）はどれも `GoodOutput` になりえない。 -/
theorem not_good_of_sameCycle_one {N : ℕ} [NeZero N] (f : Perm (Fin N))
    (hdiff : ¬ f.SameCycle (0 : Fin N) 1) {v₀ v₁ : Fin N}
    (hv : f.SameCycle 1 v₀) :
    ¬ PeriodicTM.QueryGame.GoodOutput (0 : Fin N) 1 f v₀ v₁ := by
  intro hg
  exact hdiff ((goodOutput_sameCycle_left hg).trans hv.symm)

/-- P₁ 上の点は `1` と同一軌道（`completion_pow_one` の言い換え）。 -/
theorem sameCycle_one_onP1 {N ℓ : ℕ} [NeZero N] (s : AdvState)
    (f : Perm (Fin N)) (hcomp : IsCompletion N ℓ s f) (hN : 2 ≤ N)
    (a : ℕ) (ha : a < s.k1) :
    f.SameCycle (1 : Fin N) (Fin.ofNat N (2 + s.k0 + a)) := by
  refine ⟨((a + 1 : ℕ) : ℤ), ?_⟩
  rw [zpow_natCast, ← ofNat_one_eq_one hN]
  exact completion_pow_one s f hcomp a ha

/-- **型3の具体形は別軌道完成で死ぬ**（葉での kill その1）。 -/
theorem type3_output_killed {N ℓ : ℕ} [NeZero N] (s : AdvState)
    (f : Perm (Fin N)) (hcomp : IsCompletion N ℓ s f)
    (hdiff : ¬ f.SameCycle (0 : Fin N) 1) (hN : 2 ≤ N)
    (a : ℕ) (ha : a < s.k1) (v₁ : Fin N) :
    ¬ PeriodicTM.QueryGame.GoodOutput (0 : Fin N) 1 f
      (Fin.ofNat N (2 + s.k0 + a)) v₁ :=
  not_good_of_sameCycle_one f hdiff (sameCycle_one_onP1 s f hcomp hN a ha)

/-! ### 同一軌道完成の頂点列（距離 `d`）

`0` と `1` を**同じ**長さ `ℓ` のサイクルに、向き付き距離 `d` で置く。
並びは 位置0 に `0`、`1..k₀` に P₀、`k₀+1..d−1` を未開示点で埋め（`gap`）、
位置 `d` に `1`、`d+1..d+k₁` に P₁、残りを `rest` と迷いブロックで埋める。
`gap.length = d − 1 − k₀` が距離 `d` を実現する（`k₀ < d` が必要）。 -/
def sameCycleVerts (s : AdvState) (gap rest : List ℕ) (b : List (List ℕ)) :
    List ℕ :=
  (0 :: List.range' 2 s.k0) ++ gap ++ (1 :: List.range' (2 + s.k0) s.k1) ++
    rest ++ b.flatten

/-- 同一軌道頂点列の長さ。 -/
theorem sameCycleVerts_length (s : AdvState) (gap rest : List ℕ)
    (b : List (List ℕ)) :
    (sameCycleVerts s gap rest b).length
      = 1 + s.k0 + gap.length + 1 + s.k1 + rest.length
        + (b.map List.length).sum := by
  unfold sameCycleVerts
  simp [List.length_append, List.length_range', List.length_flatten]
  omega

/-- **開示辺はすべて同一軌道頂点列の隣接**（`edges_isAdj` の同一軌道版）。
P₀ は先頭、P₁ は `gap` の直後、迷いパスは末尾のブロック内に並ぶ。 -/
theorem edges_isAdj_sameCycle (s : AdvState) (gap rest : List ℕ)
    (b : List (List ℕ)) (hcover : ∀ c ∈ s.blocks, c ∈ b) :
    ∀ p ∈ s.edges, IsAdj (sameCycleVerts s gap rest b) p.1 p.2 := by
  intro p hp
  unfold AdvState.edges at hp
  unfold sameCycleVerts
  rcases List.mem_append.mp hp with h | h
  · rcases List.mem_append.mp h with h | h
    · -- P₀: 先頭ブロックの隣接を4回持ち上げる
      exact (pathEdges_isAdj h).append_right.append_right.append_right.append_right
    · -- P₁: `gap` の直後にあるので append_left を1回挟む
      exact (pathEdges_isAdj h).append_left.append_right.append_right
  · obtain ⟨c, hc, hadj⟩ := strayEdges_mem_block s.strays (2 + s.k0 + s.k1) p h
    exact (hadj.flatten (hcover c hc)).append_left

/-- **距離が実現されること**: `1` は頂点列の位置
`d = 1 + k₀ + |gap|` にある。`formPerm` はリストの位置を 1 つ進める
置換なので、これは `1 = f^d(0)` を意味する（`gap` の長さで距離を選べる
＝ 生存距離集合 `D` の各元に対応する完成が作れる）。 -/
theorem sameCycleVerts_one_pos (s : AdvState) (gap rest : List ℕ)
    (b : List (List ℕ)) :
    (sameCycleVerts s gap rest b)[1 + s.k0 + gap.length]? = some 1 := by
  unfold sameCycleVerts
  have hlenA : (0 :: List.range' 2 s.k0).length = 1 + s.k0 := by
    simp [List.length_range']; omega
  rw [List.append_assoc, List.append_assoc, List.append_assoc,
    List.getElem?_append_right (by omega), hlenA]
  rw [List.getElem?_append_right (by omega)]
  have hidx : 1 + s.k0 + gap.length - (1 + s.k0) - gap.length = 0 := by omega
  rw [hidx]
  simp

/-- **同一軌道頂点列の Nodup**（充填を未開示点の連続区間に取った版）。
値域が `{0}∪[2,2+k₀)`／`[vc,vc+g)`／`{1}∪[2+k₀,2+k₀+k₁)`／
`[vc+g,vc+g+r)`／`[2+k₀+k₁,vc)` の5帯に分かれるので、
帯どうしの非交差はすべて omega で片づく。 -/
theorem sameCycleVerts_nodup (s : AdvState) (g r : ℕ) (b : List (List ℕ))
    (hbmem : ∀ c ∈ b, c ∈ s.blocks) (hbnd : b.Pairwise List.Disjoint)
    (hbdup : ∀ c ∈ b, c.Nodup) :
    (sameCycleVerts s (List.range' s.vertexCount g)
      (List.range' (s.vertexCount + g) r) b).Nodup := by
  have hvc : 2 + s.k0 + s.k1 ≤ s.vertexCount := by
    unfold AdvState.vertexCount; omega
  -- 各部分の値域
  have hA : ∀ x ∈ (0 :: List.range' 2 s.k0), x = 0 ∨ (2 ≤ x ∧ x < 2 + s.k0) := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | h
    · exact Or.inl rfl
    · have := List.mem_range'_1.mp h; exact Or.inr (by omega)
  have hB : ∀ x ∈ (1 :: List.range' (2 + s.k0) s.k1),
      x = 1 ∨ (2 + s.k0 ≤ x ∧ x < 2 + s.k0 + s.k1) := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | h
    · exact Or.inl rfl
    · have := List.mem_range'_1.mp h; exact Or.inr (by omega)
  have hF : ∀ x ∈ b.flatten, 2 + s.k0 + s.k1 ≤ x ∧ x < s.vertexCount := by
    intro x hx
    obtain ⟨c, hc, hxc⟩ := List.mem_flatten.mp hx
    exact blocks_mem_bound s (hbmem c hc) hxc
  have hG : ∀ x ∈ List.range' s.vertexCount g,
      s.vertexCount ≤ x ∧ x < s.vertexCount + g := fun x hx =>
    List.mem_range'_1.mp hx
  have hR : ∀ x ∈ List.range' (s.vertexCount + g) r,
      s.vertexCount + g ≤ x ∧ x < s.vertexCount + g + r := fun x hx =>
    List.mem_range'_1.mp hx
  -- 各部分の Nodup
  have nA : (0 :: List.range' 2 s.k0).Nodup :=
    List.nodup_cons.mpr ⟨fun h => by have := List.mem_range'_1.mp h; omega,
      List.nodup_range'⟩
  have nB : (1 :: List.range' (2 + s.k0) s.k1).Nodup :=
    List.nodup_cons.mpr ⟨fun h => by have := List.mem_range'_1.mp h; omega,
      List.nodup_range'⟩
  have nF : b.flatten.Nodup := List.nodup_flatten.mpr ⟨hbdup, hbnd⟩
  -- 帯どうしの非交差
  have dAG : List.Disjoint (0 :: List.range' 2 s.k0)
      (List.range' s.vertexCount g) := by
    intro x hx hx'; have := hA x hx; have := hG x hx'; omega
  have dAB : List.Disjoint (0 :: List.range' 2 s.k0)
      (1 :: List.range' (2 + s.k0) s.k1) := by
    intro x hx hx'; have := hA x hx; have := hB x hx'; omega
  have dAR : List.Disjoint (0 :: List.range' 2 s.k0)
      (List.range' (s.vertexCount + g) r) := by
    intro x hx hx'; have := hA x hx; have := hR x hx'; omega
  have dAF : List.Disjoint (0 :: List.range' 2 s.k0) b.flatten := by
    intro x hx hx'; have := hA x hx; have := hF x hx'; omega
  have dGB : List.Disjoint (List.range' s.vertexCount g)
      (1 :: List.range' (2 + s.k0) s.k1) := by
    intro x hx hx'; have := hG x hx; have := hB x hx'; omega
  have dGR : List.Disjoint (List.range' s.vertexCount g)
      (List.range' (s.vertexCount + g) r) := by
    intro x hx hx'; have := hG x hx; have := hR x hx'; omega
  have dGF : List.Disjoint (List.range' s.vertexCount g) b.flatten := by
    intro x hx hx'; have := hG x hx; have := hF x hx'; omega
  have dBR : List.Disjoint (1 :: List.range' (2 + s.k0) s.k1)
      (List.range' (s.vertexCount + g) r) := by
    intro x hx hx'; have := hB x hx; have := hR x hx'; omega
  have dBF : List.Disjoint (1 :: List.range' (2 + s.k0) s.k1) b.flatten := by
    intro x hx hx'; have := hB x hx; have := hF x hx'; omega
  have dRF : List.Disjoint (List.range' (s.vertexCount + g) r) b.flatten := by
    intro x hx hx'; have := hR x hx; have := hF x hx'; omega
  -- 積み上げ
  have n1 := nA.append (List.nodup_range' (s := s.vertexCount) (n := g)) dAG
  have d1 : List.Disjoint ((0 :: List.range' 2 s.k0) ++
      List.range' s.vertexCount g) (1 :: List.range' (2 + s.k0) s.k1) := by
    intro x hx hx'
    rcases List.mem_append.mp hx with h | h
    · exact dAB h hx'
    · exact dGB h hx'
  have n2 := n1.append nB d1
  have d2 : List.Disjoint (((0 :: List.range' 2 s.k0) ++
      List.range' s.vertexCount g) ++ (1 :: List.range' (2 + s.k0) s.k1))
      (List.range' (s.vertexCount + g) r) := by
    intro x hx hx'
    rcases List.mem_append.mp hx with h | h
    · rcases List.mem_append.mp h with h | h
      · exact dAR h hx'
      · exact dGR h hx'
    · exact dBR h hx'
  have n3 := n2.append (List.nodup_range' (s := s.vertexCount + g) (n := r)) d2
  have d3 : List.Disjoint ((((0 :: List.range' 2 s.k0) ++
      List.range' s.vertexCount g) ++ (1 :: List.range' (2 + s.k0) s.k1)) ++
      List.range' (s.vertexCount + g) r) b.flatten := by
    intro x hx hx'
    rcases List.mem_append.mp hx with h | h
    · rcases List.mem_append.mp h with h | h
      · rcases List.mem_append.mp h with h | h
        · exact dAF h hx'
        · exact dGF h hx'
      · exact dBF h hx'
    · exact dRF h hx'
  exact n3.append nF d3

/-- 同一軌道完成の置換: 1 本のサイクルの `formPerm`（残りは固定点）。 -/
def sameCyclePerm (N : ℕ) [NeZero N] (s : AdvState) (g r : ℕ)
    (b : List (List ℕ)) : Perm (Fin N) :=
  ((sameCycleVerts s (List.range' s.vertexCount g)
    (List.range' (s.vertexCount + g) r) b).map (Fin.ofNat N)).formPerm

/-- **同一軌道完成であること**。別軌道版の `buildPerm_isCompletion` と
同じ構造だが、サイクルが1本なので `l₂ = []`（`formPerm [] = 1`）と
みなして既存の補題をそのまま使う。 -/
theorem sameCyclePerm_isCompletion {N ℓ : ℕ} [NeZero N] (s : AdvState)
    (g r : ℕ) (b : List (List ℕ))
    (hlen : (sameCycleVerts s (List.range' s.vertexCount g)
      (List.range' (s.vertexCount + g) r) b).length = ℓ)
    (hlt : ∀ x ∈ sameCycleVerts s (List.range' s.vertexCount g)
      (List.range' (s.vertexCount + g) r) b, x < N)
    (hbmem : ∀ c ∈ b, c ∈ s.blocks) (hbnd : b.Pairwise List.Disjoint)
    (hbdup : ∀ c ∈ b, c.Nodup) (hcover : ∀ c ∈ s.blocks, c ∈ b) :
    IsCompletion N ℓ s (sameCyclePerm N s g r b) := by
  have hnd := sameCycleVerts_nodup s g r b hbmem hbnd hbdup
  have hLnd := ofNat_injOn (N := N) hlt hnd
  have h0mem : (0 : Fin N) ∈ (sameCycleVerts s (List.range' s.vertexCount g)
      (List.range' (s.vertexCount + g) r) b).map (Fin.ofNat N) := by
    have h : (0 : ℕ) ∈ sameCycleVerts s (List.range' s.vertexCount g)
        (List.range' (s.vertexCount + g) r) b := by
      unfold sameCycleVerts; simp
    have := List.mem_map_of_mem (f := Fin.ofNat N) h
    rwa [ofNat_zero_eq_zero] at this
  unfold sameCyclePerm
  refine ⟨?_, ?_, ?_⟩
  · exact formPerm_pow_eq_one_of_dvd hLnd (by rw [List.length_map, hlen])
  · have h := orbit_card (l₂ := ([] : List (Fin N))) hLnd
      (by intro x _ hx'; simp at hx') h0mem
    simpa [List.length_map, hlen] using h
  · intro p hp
    -- gap/rest は明示的に渡す（目標からは推論できない）
    have hadj := (edges_isAdj_sameCycle s (List.range' s.vertexCount g)
      (List.range' (s.vertexCount + g) r) b hcover p hp).map (Fin.ofNat N)
    exact formPerm_of_adjacent hLnd hadj

/-- 充填を連続区間に取った版での `1` の位置（`gap.length = g`）。 -/
theorem sameCycleVerts_one_pos' (s : AdvState) (g r : ℕ) (b : List (List ℕ)) :
    (sameCycleVerts s (List.range' s.vertexCount g)
      (List.range' (s.vertexCount + g) r) b)[1 + s.k0 + g]? = some 1 := by
  have h := sameCycleVerts_one_pos s (List.range' s.vertexCount g)
    (List.range' (s.vertexCount + g) r) b
  simpa [List.length_range'] using h

/-- **距離 `d = 1 + k₀ + g` が実現されている**:
`f^d(0) = 1`。`formPerm` はリスト上の位置を 1 つ進めるので、
`0` が位置 0、`1` が位置 `d` にあることから直ちに従う。
これで補題9.4 の型分類に現れる距離 `d` が、
`gap` の長さ `g` によって自由に選べることが確定する。 -/
theorem sameCyclePerm_pow_eq_one_vertex {N : ℕ} [NeZero N] (s : AdvState)
    (g r : ℕ) (b : List (List ℕ))
    (hlt : ∀ x ∈ sameCycleVerts s (List.range' s.vertexCount g)
      (List.range' (s.vertexCount + g) r) b, x < N)
    (hbmem : ∀ c ∈ b, c ∈ s.blocks) (hbnd : b.Pairwise List.Disjoint)
    (hbdup : ∀ c ∈ b, c.Nodup)
    (hd : 1 + s.k0 + g < (sameCycleVerts s (List.range' s.vertexCount g)
      (List.range' (s.vertexCount + g) r) b).length) :
    ((sameCyclePerm N s g r b) ^ (1 + s.k0 + g)) (Fin.ofNat N 0)
      = Fin.ofNat N 1 := by
  have hnd := sameCycleVerts_nodup s g r b hbmem hbnd hbdup
  have hLnd := ofNat_injOn (N := N) hlt hnd
  have hlenL : ((sameCycleVerts s (List.range' s.vertexCount g)
      (List.range' (s.vertexCount + g) r) b).map (Fin.ofNat N)).length
      = (sameCycleVerts s (List.range' s.vertexCount g)
        (List.range' (s.vertexCount + g) r) b).length :=
    List.length_map (Fin.ofNat N)
  have hdL : 1 + s.k0 + g < ((sameCycleVerts s (List.range' s.vertexCount g)
      (List.range' (s.vertexCount + g) r) b).map (Fin.ofNat N)).length := by
    rw [hlenL]; exact hd
  -- 位置 0 と位置 d の値
  have h0? : ((sameCycleVerts s (List.range' s.vertexCount g)
      (List.range' (s.vertexCount + g) r) b).map (Fin.ofNat N))[0]?
      = some (Fin.ofNat N 0) := by
    rw [List.getElem?_map]
    unfold sameCycleVerts
    simp
  have h1? : ((sameCycleVerts s (List.range' s.vertexCount g)
      (List.range' (s.vertexCount + g) r) b).map
      (Fin.ofNat N))[1 + s.k0 + g]? = some (Fin.ofNat N 1) := by
    rw [List.getElem?_map, sameCycleVerts_one_pos']
    rfl
  have h0 := List.getElem?_eq_getElem (l := (sameCycleVerts s
    (List.range' s.vertexCount g) (List.range' (s.vertexCount + g) r) b).map
    (Fin.ofNat N)) (i := 0) (by omega)
  have h1 := List.getElem?_eq_getElem (l := (sameCycleVerts s
    (List.range' s.vertexCount g) (List.range' (s.vertexCount + g) r) b).map
    (Fin.ofNat N)) (i := 1 + s.k0 + g) hdL
  rw [h0?] at h0
  rw [h1?] at h1
  have key := List.formPerm_pow_apply_getElem _ hLnd (1 + s.k0 + g) 0 (by omega)
  have hmod : (0 + (1 + s.k0 + g)) % ((sameCycleVerts s
      (List.range' s.vertexCount g) (List.range' (s.vertexCount + g) r) b).map
      (Fin.ofNat N)).length = 1 + s.k0 + g := by
    rw [Nat.zero_add]; exact Nat.mod_eq_of_lt hdL
  unfold sameCyclePerm
  simp only [hmod] at key
  -- `ofNat 0 → L[0]`、`ofNat 1 → L[d]` の向きに書き換える
  rw [Option.some.inj h0, Option.some.inj h1]
  exact key

/-! ### GoodOutput から座標関係へ（型1・2・4 を殺す入口）

`GoodOutput` の反射 `ι` を橋渡し（`reflection_pos_relation`）に通すと、
出力対の位置 `(α, β)` が距離 `d` に対して `β = α − d` を満たすことが
出る。距離が 2 つ残っていればこの関係は両立せず、
`survives_two_distances` により型3 以外は死ぬ。 -/

/-- **良い出力の位置関係**: `v₀ = f^α(0)`、`v₁ = f^β(0)`、`1 = f^d(0)`
のとき、`GoodOutput` なら `β = α − d`（`ZMod ℓ`）。 -/
theorem goodOutput_pos_relation {N ℓ : ℕ} [NeZero N] {f : Perm (Fin N)}
    (hcard : #{y | f.SameCycle (0 : Fin N) y} = ℓ)
    {α β d : ℕ} {v₀ v₁ : Fin N}
    (hv₀ : v₀ = (f ^ α) (0 : Fin N)) (hv₁ : v₁ = (f ^ β) (0 : Fin N))
    (hd : (1 : Fin N) = (f ^ d) (0 : Fin N))
    (hgood : PeriodicTM.QueryGame.GoodOutput (0 : Fin N) 1 f v₀ v₁) :
    (β : ZMod ℓ) = (α : ZMod ℓ) - (d : ZMod ℓ) := by
  obtain ⟨ι, ⟨hinv, _, hcc⟩, ha, hb⟩ := hgood
  refine PeriodicTM.TwoPointBridge.reflection_pos_relation hinv hcc hcard
    ?_ ?_
  · rw [ha, hv₀]
  · rw [hd] at hb
    rw [hb, hv₁]

/-- **2つの距離で同時に良い出力は存在しない（位置が同じ場合）**:
`v₀`・`v₁` の位置が距離に依らない（＝ともに P₀ 側＝型1）なら、
`d` と `d+1` の両方で良い出力にはなれない。 -/
theorem type1_killed_two_distances {N ℓ : ℕ} [NeZero N] (hℓ : 3 ≤ ℓ)
    {f g : Perm (Fin N)}
    (hcardf : #{y | f.SameCycle (0 : Fin N) y} = ℓ)
    (hcardg : #{y | g.SameCycle (0 : Fin N) y} = ℓ)
    {α β d : ℕ} {v₀ v₁ : Fin N}
    (hv₀f : v₀ = (f ^ α) (0 : Fin N)) (hv₁f : v₁ = (f ^ β) (0 : Fin N))
    (hv₀g : v₀ = (g ^ α) (0 : Fin N)) (hv₁g : v₁ = (g ^ β) (0 : Fin N))
    (hdf : (1 : Fin N) = (f ^ d) (0 : Fin N))
    (hdg : (1 : Fin N) = (g ^ (d + 1)) (0 : Fin N))
    (hgf : PeriodicTM.QueryGame.GoodOutput (0 : Fin N) 1 f v₀ v₁)
    (hgg : PeriodicTM.QueryGame.GoodOutput (0 : Fin N) 1 g v₀ v₁) :
    False := by
  haveI : Fact (1 < ℓ) := ⟨by omega⟩
  have h1 := goodOutput_pos_relation hcardf hv₀f hv₁f hdf hgf
  have h2 := goodOutput_pos_relation hcardg hv₀g hv₁g hdg hgg
  -- β = α − d と β = α − (d+1) から 1 = 0（ZMod ℓ）
  push_cast at h2
  have : (1 : ZMod ℓ) = 0 := by linear_combination h2 - h1
  exact one_ne_zero this

/-- **型2の2距離撃墜**: `v₀` が P₀ 側（位置 `α`、距離に依らない）、
`v₁` が P₁ 側（位置 `d + β`）の出力は、距離 `d` と `d+1` の両方では
良い出力になれない。`2d = 2(d+1)` すなわち `2 = 0` に帰着し、
`ℓ ≥ 3` に矛盾する（偶奇に依らない）。 -/
theorem type2_killed_two_distances {N ℓ : ℕ} [NeZero N] (hℓ : 3 ≤ ℓ)
    {f g : Perm (Fin N)}
    (hcardf : #{y | f.SameCycle (0 : Fin N) y} = ℓ)
    (hcardg : #{y | g.SameCycle (0 : Fin N) y} = ℓ)
    {α β d : ℕ} {v₀ v₁ : Fin N}
    (hv₀f : v₀ = (f ^ α) (0 : Fin N)) (hv₀g : v₀ = (g ^ α) (0 : Fin N))
    (hv₁f : v₁ = (f ^ (d + β)) (0 : Fin N))
    (hv₁g : v₁ = (g ^ ((d + 1) + β)) (0 : Fin N))
    (hdf : (1 : Fin N) = (f ^ d) (0 : Fin N))
    (hdg : (1 : Fin N) = (g ^ (d + 1)) (0 : Fin N))
    (hgf : PeriodicTM.QueryGame.GoodOutput (0 : Fin N) 1 f v₀ v₁)
    (hgg : PeriodicTM.QueryGame.GoodOutput (0 : Fin N) 1 g v₀ v₁) :
    False := by
  have h1 := goodOutput_pos_relation hcardf hv₀f hv₁f hdf hgf
  have h2 := goodOutput_pos_relation hcardg hv₀g hv₁g hdg hgg
  push_cast at h1 h2
  have h2eq : (2 : ZMod ℓ) = 0 := by linear_combination h2 - h1
  exact PeriodicTM.TwoPointCore.two_ne_zero hℓ h2eq

/-- **型4の2距離撃墜**: 両成分とも P₁ 側（位置 `d + α`, `d + β`）の
出力も、距離が 2 つ残っていれば死ぬ（`1 = 0` に帰着）。 -/
theorem type4_killed_two_distances {N ℓ : ℕ} [NeZero N] (hℓ : 3 ≤ ℓ)
    {f g : Perm (Fin N)}
    (hcardf : #{y | f.SameCycle (0 : Fin N) y} = ℓ)
    (hcardg : #{y | g.SameCycle (0 : Fin N) y} = ℓ)
    {α β d : ℕ} {v₀ v₁ : Fin N}
    (hv₀f : v₀ = (f ^ (d + α)) (0 : Fin N))
    (hv₀g : v₀ = (g ^ ((d + 1) + α)) (0 : Fin N))
    (hv₁f : v₁ = (f ^ (d + β)) (0 : Fin N))
    (hv₁g : v₁ = (g ^ ((d + 1) + β)) (0 : Fin N))
    (hdf : (1 : Fin N) = (f ^ d) (0 : Fin N))
    (hdg : (1 : Fin N) = (g ^ (d + 1)) (0 : Fin N))
    (hgf : PeriodicTM.QueryGame.GoodOutput (0 : Fin N) 1 f v₀ v₁)
    (hgg : PeriodicTM.QueryGame.GoodOutput (0 : Fin N) 1 g v₀ v₁) :
    False := by
  haveI : Fact (1 < ℓ) := ⟨by omega⟩
  have h1 := goodOutput_pos_relation hcardf hv₀f hv₁f hdf hgf
  have h2 := goodOutput_pos_relation hcardg hv₀g hv₁g hdg hgg
  push_cast at h1 h2
  have hone : (1 : ZMod ℓ) = 0 := by linear_combination h2 - h1
  exact one_ne_zero hone

/-! ### 対局と実行の一致（葉での撃墜を木全体へ渡す）

敵対者の答えと完成 `f` の値が各手で一致していれば、木を `f` に対して
走らせたときに辿り着く葉は、対局で辿った葉と同じ。したがって
「対局が辿った葉の出力が `f` に対して良くない」ことを示せば、
その木は `f` に負ける。 -/

/-- 対局が辿り着く葉の出力対。 -/
def playLeaf {N : ℕ} (σ : Strategy N) :
    {q : ℕ} → PeriodicTM.QueryGame.Tree N q → AdvState → Fin N × Fin N
  | _, .leaf v₀ v₁, _ => (v₀, v₁)
  | _, .node x child, s =>
      playLeaf σ (child (σ.answer s x)) (s.step (σ.kind s x))

/-- 完成 `f` が対局の答えと各手で一致する。 -/
def Agrees {N : ℕ} (σ : Strategy N) (f : Perm (Fin N)) :
    {q : ℕ} → PeriodicTM.QueryGame.Tree N q → AdvState → Prop
  | _, .leaf _ _, _ => True
  | _, .node x child, s =>
      f x = σ.answer s x ∧
        Agrees σ f (child (σ.answer s x)) (s.step (σ.kind s x))

/-- **一致すれば同じ葉に着く**: `Runs`（木を `f` に対して走らせる）は、
対局が辿った葉の出力が `f` にとって良いことと同値。 -/
theorem runs_iff_goodOutput_playLeaf {N : ℕ} (a b : Fin N) (σ : Strategy N)
    (f : Perm (Fin N)) :
    ∀ {q : ℕ} (t : PeriodicTM.QueryGame.Tree N q) (s : AdvState),
      Agrees σ f t s →
      (PeriodicTM.QueryGame.Runs a b t f ↔
        PeriodicTM.QueryGame.GoodOutput a b f (playLeaf σ t s).1
          (playLeaf σ t s).2)
  | _, .leaf v₀ v₁, s, _ => Iff.rfl
  | _, .node x child, s, h => by
    obtain ⟨hx, hrest⟩ := h
    show PeriodicTM.QueryGame.Runs a b (child (f x)) f ↔ _
    rw [hx]
    exact runs_iff_goodOutput_playLeaf a b σ f (child (σ.answer s x))
      (s.step (σ.kind s x)) hrest

/-- **木が勝てないことの十分条件**: 対局が辿った葉の出力が、
対局と一致するある完成 `f`（約束を満たす）に対して良くなければ、
その木は勝利戦略ではない。 -/
theorem not_winsAt_of_bad_leaf {N n ℓ : ℕ} (a b : Fin N) (σ : Strategy N)
    {q : ℕ} (t : PeriodicTM.QueryGame.Tree N q) (s : AdvState)
    (f : Perm (Fin N)) (hvalid : PeriodicTM.QueryGame.Valid n ℓ a f)
    (hagree : Agrees σ f t s)
    (hbad : ¬ PeriodicTM.QueryGame.GoodOutput a b f (playLeaf σ t s).1
      (playLeaf σ t s).2) :
    ¬ PeriodicTM.QueryGame.WinsAt n ℓ a b t := by
  intro hwin
  exact hbad ((runs_iff_goodOutput_playLeaf a b σ f t s hagree).mp
    (hwin f hvalid))

/-! ### 付け替え（共役）による輸送

`research/17` の設計判断: グループ順の埋め込みで得た完成を、
具体的な対局に現れた標識へ移すために、共役 `τ * f * τ⁻¹` に対する
不変性を用意する。`IsReflection`・`GoodOutput` は共役で移る。 -/

/-- 反射は共役で移る（`ι ↦ τ ∘ ι ∘ τ⁻¹`）。 -/
theorem isReflection_conj {N : ℕ} (τ : Perm (Fin N)) {f : Perm (Fin N)}
    {ι : Fin N → Fin N} (h : PeriodicTM.QueryGame.IsReflection f ι) :
    PeriodicTM.QueryGame.IsReflection (τ * f * τ⁻¹)
      (fun x => τ (ι (τ⁻¹ x))) := by
  obtain ⟨hinv, horb, hcc⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro x
    simp [hinv]
  · intro x
    have := (horb (τ⁻¹ x)).conj (g := τ)
    simpa using this
  · intro x
    simp [hcc]

/-- 良い出力も共役で移る。これで「グループ順の標識で構成した完成」を
「対局に現れた標識」へ運べる。 -/
theorem goodOutput_conj {N : ℕ} (τ : Perm (Fin N)) {f : Perm (Fin N)}
    {a b v₀ v₁ : Fin N}
    (h : PeriodicTM.QueryGame.GoodOutput a b f v₀ v₁) :
    PeriodicTM.QueryGame.GoodOutput (τ a) (τ b) (τ * f * τ⁻¹) (τ v₀)
      (τ v₁) := by
  obtain ⟨ι, hrefl, ha, hb⟩ := h
  refine ⟨fun x => τ (ι (τ⁻¹ x)), isReflection_conj τ hrefl, ?_, ?_⟩
  · simp [ha]
  · simp [hb]

/-- 共役の冪: `(τ f τ⁻¹)^n = τ f^n τ⁻¹`。位数条件の輸送に使う。 -/
theorem conj_pow {N : ℕ} (τ f : Perm (Fin N)) (n : ℕ) :
    (τ * f * τ⁻¹) ^ n = τ * f ^ n * τ⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, pow_succ]; group

/-- 位数条件は共役で保たれる。 -/
theorem conj_pow_eq_one {N ℓ : ℕ} (τ f : Perm (Fin N)) (h : f ^ ℓ = 1) :
    (τ * f * τ⁻¹) ^ ℓ = 1 := by
  rw [conj_pow, h]; group

/-- 同一軌道関係は共役で移る（両方向）。 -/
theorem sameCycle_conj_iff {N : ℕ} (τ f : Perm (Fin N)) (x y : Fin N) :
    (τ * f * τ⁻¹).SameCycle (τ x) (τ y) ↔ f.SameCycle x y := by
  constructor
  · intro h
    have h2 := h.conj (g := τ⁻¹)
    have heq : τ⁻¹ * (τ * f * τ⁻¹) * τ⁻¹⁻¹ = f := by group
    rw [heq] at h2
    simpa using h2
  · intro h
    exact h.conj

/-- **軌道の大きさは共役で保たれる**（`τ` による全単射で移る）。
`IsCompletion` の軌道長条件を付け替え先へ運ぶのに使う。 -/
theorem orbit_card_conj {N : ℕ} (τ f : Perm (Fin N)) (x : Fin N) :
    #{y | (τ * f * τ⁻¹).SameCycle (τ x) y} = #{y | f.SameCycle x y} := by
  have hset : ({y | (τ * f * τ⁻¹).SameCycle (τ x) y} : Finset (Fin N))
      = ({y | f.SameCycle x y} : Finset (Fin N)).map τ.toEmbedding := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Equiv.coe_toEmbedding]
    constructor
    · intro h
      refine ⟨τ⁻¹ z, ?_, by simp⟩
      exact (sameCycle_conj_iff τ f x (τ⁻¹ z)).mp (by simpa using h)
    · rintro ⟨w, hw, rfl⟩
      exact (sameCycle_conj_iff τ f x w).mpr hw
  rw [hset, Finset.card_map]

/-- **共役した置換は付け替え先の完成**: `τ` が指定点 `0` を固定するなら、
`τ f τ⁻¹` は位数条件と軌道長条件を満たし、辺は `τ` で写した先を尊重する。
（`research/17` の手順1の到達点。グループ順で作った完成を、対局に
現れた標識へ運ぶ。） -/
theorem isCompletion_conj {N ℓ : ℕ} [NeZero N] (s : AdvState)
    (τ f : Perm (Fin N)) (hτ0 : τ (0 : Fin N) = 0)
    (hcomp : IsCompletion N ℓ s f) :
    (τ * f * τ⁻¹) ^ ℓ = 1 ∧
      #{y | (τ * f * τ⁻¹).SameCycle (0 : Fin N) y} = ℓ ∧
      ∀ p ∈ s.edges, (τ * f * τ⁻¹) (τ (Fin.ofNat N p.1))
        = τ (Fin.ofNat N p.2) := by
  obtain ⟨hpow, hcard, hedge⟩ := hcomp
  refine ⟨conj_pow_eq_one τ f hpow, ?_, ?_⟩
  · have h := orbit_card_conj τ f (0 : Fin N)
    rw [hτ0] at h
    rw [h, hcard]
  · intro p hp
    -- 注: `Perm.inv_apply_self` という名前は無い（exact? で確認）。
    -- τ⁻¹(τ x) = x は `Perm.inv_eq_iff_eq.mpr rfl` で出る
    have hinv : ∀ x : Fin N, τ⁻¹ (τ x) = x :=
      fun x => Perm.inv_eq_iff_eq.mpr rfl
    simp only [Perm.mul_apply, hinv]
    rw [hedge p hp]

/-- 別軌道性も共役で保たれる（`τ` が `0` と `1` を固定するとき）。 -/
theorem not_sameCycle_conj {N : ℕ} [NeZero N] (τ f : Perm (Fin N))
    (hτ0 : τ (0 : Fin N) = 0) (hτ1 : τ (1 : Fin N) = 1)
    (h : ¬ f.SameCycle (0 : Fin N) 1) :
    ¬ (τ * f * τ⁻¹).SameCycle (0 : Fin N) 1 := by
  intro hc
  refine h ((sameCycle_conj_iff τ f 0 1).mp ?_)
  rwa [hτ0, hτ1]

/-! ### 付け替えの存在（`research/17` の手順3の鍵）

2 通りの標識付け（対局の allocation 順 と 埋め込みのグループ順）は
どちらも「スロット → `Fin N`」の単射なので、両者を結ぶ置換が取れる。
mathlib の `Equiv.Perm.exists_extending_pair` がそのまま使える。 -/

/-- 2つの単射を結ぶ置換の存在。 -/
theorem exists_relabeling {N m : ℕ} (u v : Fin m → Fin N)
    (hu : Function.Injective u) (hv : Function.Injective v) :
    ∃ τ : Perm (Fin N), ∀ i, τ (u i) = v i :=
  Perm.exists_extending_pair u v hu hv

/-- **指定点を共有する標識付けの付け替えは `0` と `1` を固定する**。
`isCompletion_conj` / `not_sameCycle_conj` の仮定がそのまま満たされる。 -/
theorem exists_relabeling_fixing {N m : ℕ} [NeZero N] (u v : Fin m → Fin N)
    (hu : Function.Injective u) (hv : Function.Injective v)
    {i0 i1 : Fin m} (hu0 : u i0 = 0) (hv0 : v i0 = 0)
    (hu1 : u i1 = 1) (hv1 : v i1 = 1) :
    ∃ τ : Perm (Fin N), (∀ i, τ (u i) = v i) ∧ τ 0 = 0 ∧ τ 1 = 1 := by
  obtain ⟨τ, hτ⟩ := exists_relabeling u v hu hv
  refine ⟨τ, hτ, ?_, ?_⟩
  · have h := hτ i0
    rwa [hu0, hv0] at h
  · have h := hτ i1
    rwa [hu1, hv1] at h

/-! ### allocation 順の具体状態（`research/17` の手順2）

対局中に実際に現れる標識を、開示された順に持つ状態。抽象状態
`AdvState`（形だけを持つ）とは別に、`Fin N` の具体的な頂点と辺を記録する。
`used` が Nodup なのが要（付け替え `τ` を作るための単射性）。 -/

/-- 対局中の具体状態: 開示済み頂点（allocation 順）と開示済み辺。 -/
structure ConcState (N : ℕ) where
  used : List (Fin N)
  edges : List (Fin N × Fin N)

/-- まだ使っていない頂点のうち最小のもの。 -/
def freshVertex (N : ℕ) (used : List (Fin N)) : Option (Fin N) :=
  (List.finRange N).find? (fun v => decide (v ∉ used))

/-- 新鮮な頂点は未使用（`find?` の述語から）。 -/
theorem freshVertex_not_mem {N : ℕ} {used : List (Fin N)} {v : Fin N}
    (h : freshVertex N used = some v) : v ∉ used := by
  have hp := List.find?_some h
  simpa using hp

/-- 新鮮応答: 既に答えの決まっている点はその答え、そうでなければ
未使用の頂点を1つ割り当てる。 -/
def concAnswer {N : ℕ} (c : ConcState N) (x : Fin N) : Fin N :=
  match c.edges.find? (fun p => decide (p.1 = x)) with
  | some p => p.2
  | none => (freshVertex N c.used).getD x

/-- 具体状態の更新（新しい点を開示したときだけ伸びる）。 -/
def concStep {N : ℕ} (c : ConcState N) (x : Fin N) : ConcState N :=
  match c.edges.find? (fun p => decide (p.1 = x)) with
  | some _ => c
  | none =>
      match freshVertex N c.used with
      | some v => ⟨c.used ++ [v], c.edges ++ [(x, v)]⟩
      | none => c

/-- **allocation 順の標識は重複しない**: `used` は Nodup を保つ。
これが付け替え `τ` を作るための単射性を与える。 -/
theorem concStep_used_nodup {N : ℕ} (c : ConcState N) (x : Fin N)
    (h : c.used.Nodup) : (concStep c x).used.Nodup := by
  unfold concStep
  cases hfind : c.edges.find? (fun p => decide (p.1 = x)) with
  | some p => simpa using h
  | none =>
    cases hfresh : freshVertex N c.used with
    | none => simpa using h
    | some v =>
      have hdisj : List.Disjoint c.used [v] := by
        intro a ha hb
        rw [List.mem_singleton] at hb
        subst hb
        exact freshVertex_not_mem hfresh ha
      exact List.Nodup.append h (List.nodup_singleton v) hdisj

/-- **未使用頂点は残っている**: 開示済みが `N` 個未満なら新鮮な点が取れる。 -/
theorem freshVertex_isSome {N : ℕ} {used : List (Fin N)} (hnd : used.Nodup)
    (h : used.length < N) : ∃ v, freshVertex N used = some v := by
  rcases hfind : freshVertex N used with _ | v
  · exfalso
    have hall : ∀ a ∈ List.finRange N, ¬ (a ∉ used) := by
      intro a ha
      have := List.find?_eq_none.mp hfind a ha
      simpa using this
    have hsub : (Finset.univ : Finset (Fin N)) ⊆ used.toFinset := by
      intro a _
      rw [List.mem_toFinset]
      by_contra hc
      exact hall a (List.mem_finRange a) hc
    have hcard : (Finset.univ : Finset (Fin N)).card ≤ used.toFinset.card :=
      Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup hnd] at hcard
    simp at hcard
    omega
  · exact ⟨v, rfl⟩

/-- **答えは辺として記録される**: 1手進めた状態の辺集合には
`(x, concAnswer c x)` が入っている。したがって「最終状態の辺をすべて
尊重する完成」は、各手の答えとも一致する（`Agrees` の核）。 -/
theorem concAnswer_mem_edges {N : ℕ} (c : ConcState N) (x : Fin N)
    (hnd : c.used.Nodup) (h : c.used.length < N) :
    (x, concAnswer c x) ∈ (concStep c x).edges := by
  unfold concAnswer concStep
  cases hfind : c.edges.find? (fun p => decide (p.1 = x)) with
  | some p =>
    have hp := List.mem_of_find?_eq_some hfind
    have hx : p.1 = x := by
      have := List.find?_some hfind
      simpa using this
    -- `(x, p.2) = p`（Prod の eta と `hx : p.1 = x`）
    have heq : (x, p.2) = p := by rw [← hx]
    rw [heq]
    exact hp
  | none =>
    obtain ⟨v, hv⟩ := freshVertex_isSome hnd h
    simp only [hv]
    simp

/-- 辺は減らない（単調）。 -/
theorem concStep_edges_subset {N : ℕ} (c : ConcState N) (x : Fin N) :
    c.edges ⊆ (concStep c x).edges := by
  unfold concStep
  cases hfind : c.edges.find? (fun p => decide (p.1 = x)) with
  | some p => exact fun a ha => ha
  | none =>
    cases hfresh : freshVertex N c.used with
    | none => exact fun a ha => ha
    | some v => exact fun a ha => List.mem_append.mpr (Or.inl ha)

/-- 開示済み頂点は 1 手で高々 1 個増える。 -/
theorem concStep_used_length_le {N : ℕ} (c : ConcState N) (x : Fin N) :
    (concStep c x).used.length ≤ c.used.length + 1 := by
  unfold concStep
  cases hfind : c.edges.find? (fun p => decide (p.1 = x)) with
  | some p => simp
  | none =>
    cases hfresh : freshVertex N c.used with
    | none => simp
    | some v => simp

/-! ### 具体的な対局（allocation 順） -/

/-- 具体状態での対局（新鮮応答戦略に固定）。 -/
def concPlay {N : ℕ} :
    {q : ℕ} → PeriodicTM.QueryGame.Tree N q → ConcState N → ConcState N
  | _, .leaf _ _, c => c
  | _, .node x child, c => concPlay (child (concAnswer c x)) (concStep c x)

/-- 具体的な対局が辿り着く葉の出力対。 -/
def concPlayLeaf {N : ℕ} :
    {q : ℕ} → PeriodicTM.QueryGame.Tree N q → ConcState N → Fin N × Fin N
  | _, .leaf v₀ v₁, _ => (v₀, v₁)
  | _, .node x child, c =>
      concPlayLeaf (child (concAnswer c x)) (concStep c x)

/-- 対局を通じて辺は減らない。 -/
theorem concPlay_edges_subset {N : ℕ} :
    ∀ {q : ℕ} (t : PeriodicTM.QueryGame.Tree N q) (c : ConcState N),
      c.edges ⊆ (concPlay t c).edges
  | _, .leaf _ _, c => fun a ha => ha
  | _, .node x child, c => by
    intro a ha
    exact concPlay_edges_subset (child (concAnswer c x)) (concStep c x)
      (concStep_edges_subset c x ha)

/-- 対局を通じて `used` は Nodup を保ち、長さは高々 `q` しか増えない。 -/
theorem concPlay_used_nodup {N : ℕ} :
    ∀ {q : ℕ} (t : PeriodicTM.QueryGame.Tree N q) (c : ConcState N),
      c.used.Nodup → (concPlay t c).used.Nodup
  | _, .leaf _ _, c, h => h
  | _, .node x child, c, h =>
    concPlay_used_nodup (child (concAnswer c x)) (concStep c x)
      (concStep_used_nodup c x h)

theorem concPlay_used_length_le {N : ℕ} :
    ∀ {q : ℕ} (t : PeriodicTM.QueryGame.Tree N q) (c : ConcState N),
      (concPlay t c).used.length ≤ c.used.length + q
  | _, .leaf _ _, c => by simp [concPlay]
  | _, .node x child, c => by
    have h1 := concPlay_used_length_le (child (concAnswer c x)) (concStep c x)
    have h2 := concStep_used_length_le c x
    simp only [concPlay]
    omega

/-- **最終状態の完成は各手の答えと一致する（帰納）**。
`f` が対局終了時の辺をすべて尊重すれば、木を `f` に対して走らせたときに
辿り着く葉は具体的な対局が辿った葉と同じ。
これが `research/17` の手順3（`Agrees` の充足）の実体である。
（`c.used.length + q < N` は各手で新鮮な点が残っていることの保証。） -/
theorem runs_iff_good_concPlayLeaf {N : ℕ} (a b : Fin N) (f : Perm (Fin N)) :
    ∀ {q : ℕ} (t : PeriodicTM.QueryGame.Tree N q) (c : ConcState N),
      c.used.Nodup → c.used.length + q < N →
      (∀ p ∈ (concPlay t c).edges, f p.1 = p.2) →
      (PeriodicTM.QueryGame.Runs a b t f ↔
        PeriodicTM.QueryGame.GoodOutput a b f (concPlayLeaf t c).1
          (concPlayLeaf t c).2)
  | _, .leaf v₀ v₁, c, _, _, _ => Iff.rfl
  | q + 1, .node x child, c, hnd, hlen, hedges => by
    -- 各手の答えは辺として記録されており、`f` はそれを尊重する
    have hmem : (x, concAnswer c x) ∈ (concPlay (child (concAnswer c x))
        (concStep c x)).edges :=
      concPlay_edges_subset _ _ (concAnswer_mem_edges c x hnd (by omega))
    have hfx : f x = concAnswer c x := hedges _ hmem
    show PeriodicTM.QueryGame.Runs a b (child (f x)) f ↔ _
    rw [hfx]
    exact runs_iff_good_concPlayLeaf a b f (child (concAnswer c x))
      (concStep c x) (concStep_used_nodup c x hnd)
      (by have := concStep_used_length_le c x; omega) hedges

/-- **木が勝てないことの具体形**: 対局が辿った葉の出力が、対局の辺を
尊重するある完成 `f`（約束を満たす）に対して良くなければ、その木は
勝利戦略ではない。`not_winsAt_of_bad_leaf` の allocation 順版。 -/
theorem not_winsAt_of_bad_concLeaf {N n ℓ : ℕ} (a b : Fin N)
    {q : ℕ} (t : PeriodicTM.QueryGame.Tree N q) (c : ConcState N)
    (hnd : c.used.Nodup) (hlen : c.used.length + q < N)
    (f : Perm (Fin N)) (hvalid : PeriodicTM.QueryGame.Valid n ℓ a f)
    (hedges : ∀ p ∈ (concPlay t c).edges, f p.1 = p.2)
    (hbad : ¬ PeriodicTM.QueryGame.GoodOutput a b f (concPlayLeaf t c).1
      (concPlayLeaf t c).2) :
    ¬ PeriodicTM.QueryGame.WinsAt n ℓ a b t := by
  intro hwin
  exact hbad ((runs_iff_good_concPlayLeaf a b f t c hnd hlen hedges).mp
    (hwin f hvalid))

/-! ### 開示辺は部分関数（同じ始点が2度出ない）

具体状態から抽象状態（形）を読み取るための構造不変量。新鮮応答は
「まだ答えていない点」にしか新しい辺を作らないので、始点は重複しない。 -/

/-- 辺の始点に重複がない。 -/
def SourcesNodup {N : ℕ} (c : ConcState N) : Prop :=
  (c.edges.map Prod.fst).Nodup

/-- **始点の重複しなさは1手で保たれる**。 -/
theorem concStep_sources_nodup {N : ℕ} (c : ConcState N) (x : Fin N)
    (h : SourcesNodup c) : SourcesNodup (concStep c x) := by
  unfold SourcesNodup concStep
  cases hfind : c.edges.find? (fun p => decide (p.1 = x)) with
  | some p => exact h
  | none =>
    cases hfresh : freshVertex N c.used with
    | none => exact h
    | some v =>
      have hx : x ∉ c.edges.map Prod.fst := by
        intro hmem
        obtain ⟨p, hp, hpx⟩ := List.mem_map.mp hmem
        have := List.find?_eq_none.mp hfind p hp
        simp [hpx] at this
      have hdisj : List.Disjoint (c.edges.map Prod.fst) [x] := by
        intro a ha hb
        rw [List.mem_singleton] at hb
        subst hb
        exact hx ha
      simpa using List.Nodup.append h (List.nodup_singleton x) hdisj

/-- 対局を通じても始点は重複しない。 -/
theorem concPlay_sources_nodup {N : ℕ} :
    ∀ {q : ℕ} (t : PeriodicTM.QueryGame.Tree N q) (c : ConcState N),
      SourcesNodup c → SourcesNodup (concPlay t c)
  | _, .leaf _ _, c, h => h
  | _, .node x child, c, h =>
    concPlay_sources_nodup (child (concAnswer c x)) (concStep c x)
      (concStep_sources_nodup c x h)

/-! ### パスは合流しない（辺の終点は常に新規頂点）

新鮮応答の答えは必ず未使用の点なので、終点は互いに異なり、
既出の点と重ならない。これが「開示部分は互いに素な有向パスの族」
（research/09 の敵対者不変量 (i)）の Lean 版である。 -/

/-- 辺の終点はすべて開示済み頂点に入っている。 -/
def TargetsInUsed {N : ℕ} (c : ConcState N) : Prop :=
  ∀ p ∈ c.edges, p.2 ∈ c.used

/-- 辺の終点に重複がない（＝パスは合流しない）。 -/
def TargetsNodup {N : ℕ} (c : ConcState N) : Prop :=
  (c.edges.map Prod.snd).Nodup

theorem concStep_targets_in_used {N : ℕ} (c : ConcState N) (x : Fin N)
    (h : TargetsInUsed c) : TargetsInUsed (concStep c x) := by
  unfold TargetsInUsed concStep
  cases hfind : c.edges.find? (fun p => decide (p.1 = x)) with
  | some p => exact h
  | none =>
    cases hfresh : freshVertex N c.used with
    | none => exact h
    | some v =>
      intro p hp
      rcases List.mem_append.mp hp with hp' | hp'
      · exact List.mem_append.mpr (Or.inl (h p hp'))
      · rw [List.mem_singleton] at hp'
        subst hp'
        exact List.mem_append.mpr (Or.inr (List.mem_singleton_self v))

/-- **合流しないことは1手で保たれる**（新しい終点は未使用だから）。 -/
theorem concStep_targets_nodup {N : ℕ} (c : ConcState N) (x : Fin N)
    (h1 : TargetsInUsed c) (h2 : TargetsNodup c) :
    TargetsNodup (concStep c x) := by
  unfold TargetsNodup concStep
  cases hfind : c.edges.find? (fun p => decide (p.1 = x)) with
  | some p => exact h2
  | none =>
    cases hfresh : freshVertex N c.used with
    | none => exact h2
    | some v =>
      have hv : v ∉ c.edges.map Prod.snd := by
        intro hmem
        obtain ⟨p, hp, hpv⟩ := List.mem_map.mp hmem
        exact freshVertex_not_mem hfresh (hpv ▸ h1 p hp)
      have hdisj : List.Disjoint (c.edges.map Prod.snd) [v] := by
        intro a ha hb
        rw [List.mem_singleton] at hb
        subst hb
        exact hv ha
      simpa using List.Nodup.append h2 (List.nodup_singleton v) hdisj

/-- 対局を通じても保たれる。 -/
theorem concPlay_targets {N : ℕ} :
    ∀ {q : ℕ} (t : PeriodicTM.QueryGame.Tree N q) (c : ConcState N),
      TargetsInUsed c → TargetsNodup c →
      TargetsInUsed (concPlay t c) ∧ TargetsNodup (concPlay t c)
  | _, .leaf _ _, c, h1, h2 => ⟨h1, h2⟩
  | _, .node x child, c, h1, h2 =>
    concPlay_targets (child (concAnswer c x)) (concStep c x)
      (concStep_targets_in_used c x h1) (concStep_targets_nodup c x h1 h2)

/-! ### 辺の本数 ＝ 抽象状態の `q`

開示辺の本数は「情報の増えたクエリ」の回数であり、抽象状態の
`AdvState.q` に対応する。深さ `q` の木では高々 `q` 本しか増えない。 -/

theorem concStep_edges_length_le {N : ℕ} (c : ConcState N) (x : Fin N) :
    (concStep c x).edges.length ≤ c.edges.length + 1 := by
  unfold concStep
  cases hfind : c.edges.find? (fun p => decide (p.1 = x)) with
  | some p => simp
  | none =>
    cases hfresh : freshVertex N c.used with
    | none => simp
    | some v => simp

/-- **辺は深さの分しか増えない**（抽象側の `play_q_le` に対応）。 -/
theorem concPlay_edges_length_le {N : ℕ} :
    ∀ {q : ℕ} (t : PeriodicTM.QueryGame.Tree N q) (c : ConcState N),
      (concPlay t c).edges.length ≤ c.edges.length + q
  | _, .leaf _ _, c => by simp [concPlay]
  | _, .node x child, c => by
    have h1 := concPlay_edges_length_le (child (concAnswer c x)) (concStep c x)
    have h2 := concStep_edges_length_le c x
    simp only [concPlay]
    omega

/-! ### パスを辿る（抽象状態の `k₀` / `k₁` を読む道具）

`followLen edges fuel x` は `x` から辺を辿れる回数。`fuel` は停止性のため
（辺の本数を渡せば十分。パス森なので同じ点は2度通らない）。 -/

def followLen {N : ℕ} (edges : List (Fin N × Fin N)) : ℕ → Fin N → ℕ
  | 0, _ => 0
  | fuel + 1, x =>
      match edges.find? (fun p => decide (p.1 = x)) with
      | some p => followLen edges fuel p.2 + 1
      | none => 0

theorem followLen_le_fuel {N : ℕ} (edges : List (Fin N × Fin N)) :
    ∀ (fuel : ℕ) (x : Fin N), followLen edges fuel x ≤ fuel
  | 0, _ => by simp [followLen]
  | fuel + 1, x => by
    unfold followLen
    cases hfind : edges.find? (fun p => decide (p.1 = x)) with
    | some p =>
      have := followLen_le_fuel edges fuel p.2
      simp only []
      omega
    | none => simp

end PeriodicTM.ClaimA

#print axioms PeriodicTM.ClaimA.AdvState.steps_q_le
#print axioms PeriodicTM.ClaimA.concPlay_edges_length_le
#print axioms PeriodicTM.ClaimA.concPlay_targets
#print axioms PeriodicTM.ClaimA.concPlay_sources_nodup
#print axioms PeriodicTM.ClaimA.not_winsAt_of_bad_concLeaf
#print axioms PeriodicTM.ClaimA.concPlay_edges_subset
#print axioms PeriodicTM.ClaimA.concAnswer_mem_edges
#print axioms PeriodicTM.ClaimA.concStep_used_nodup
#print axioms PeriodicTM.ClaimA.exists_relabeling_fixing
#print axioms PeriodicTM.ClaimA.isCompletion_conj
#print axioms PeriodicTM.ClaimA.orbit_card_conj
#print axioms PeriodicTM.ClaimA.goodOutput_conj
#print axioms PeriodicTM.ClaimA.not_winsAt_of_bad_leaf
#print axioms PeriodicTM.ClaimA.type2_killed_two_distances
#print axioms PeriodicTM.ClaimA.type4_killed_two_distances
#print axioms PeriodicTM.ClaimA.type1_killed_two_distances
#print axioms PeriodicTM.ClaimA.sameCyclePerm_pow_eq_one_vertex
#print axioms PeriodicTM.ClaimA.sameCyclePerm_isCompletion
#print axioms PeriodicTM.ClaimA.sameCycleVerts_nodup
#print axioms PeriodicTM.ClaimA.sameCycleVerts_one_pos
#print axioms PeriodicTM.ClaimA.edges_isAdj_sameCycle
#print axioms PeriodicTM.ClaimA.type3_output_killed
#print axioms PeriodicTM.ClaimA.completion_onP1_pos
#print axioms PeriodicTM.ClaimA.completion_pow_zero
#print axioms PeriodicTM.ClaimA.play_inLowerRegion
