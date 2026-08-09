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

open Equiv

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

end PeriodicTM.ClaimA

#print axioms PeriodicTM.ClaimA.AdvState.steps_q_le
#print axioms PeriodicTM.ClaimA.sameCyclePerm_isCompletion
#print axioms PeriodicTM.ClaimA.sameCycleVerts_nodup
#print axioms PeriodicTM.ClaimA.sameCycleVerts_one_pos
#print axioms PeriodicTM.ClaimA.edges_isAdj_sameCycle
#print axioms PeriodicTM.ClaimA.type3_output_killed
#print axioms PeriodicTM.ClaimA.completion_onP1_pos
#print axioms PeriodicTM.ClaimA.completion_pow_zero
#print axioms PeriodicTM.ClaimA.play_inLowerRegion
