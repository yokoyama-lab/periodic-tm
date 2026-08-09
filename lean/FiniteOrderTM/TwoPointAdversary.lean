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
import FiniteOrderTM.TwoPointClaimA

namespace PeriodicTM.ClaimA

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

end PeriodicTM.ClaimA

#print axioms PeriodicTM.ClaimA.AdvState.steps_q_le
