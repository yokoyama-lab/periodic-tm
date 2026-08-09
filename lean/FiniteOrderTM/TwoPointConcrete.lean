/-
FiniteOrderTM/TwoPointConcrete.lean
— 新鮮応答敵対者の**具体**状態と対局（research/17 の修正方針 2・3）

`research/17` は `Strategy N`（`AdvState → Fin N → Fin N`）で具体戦略を
書く案を挙げたが、これは実際には定義できない: 新鮮な答えは「過去に
使った具体的な点」を避ける必要があり、抽象状態 `AdvState` からは
計算できない（迷いパスの開始点は**アルゴリズム側が選ぶ**ので、
使用済み集合は抽象状態に写らない）。そこで本ファイルは、実際の
頂点リストを持つ具体状態 `ConcState` の上で対局を定義する。

構成:
* `ConcState` — 0-パス・1-パス・迷いパスの具体頂点リスト。
  `paths`（パスのリスト）、`used`（開示頂点、グループ順に整列）、
  `edges`（開示辺 = 各パスの隣接対 `zip l l.tail`）、抽象化 `toAdv`。
* 敵対者の応答 `answer`（記録済みの後続があればそれ、なければ未使用点）
  と状態遷移 `step`。分岐は場合分け補題 `step_eq` に一度だけ集約する。
* 木に沿った対局 `playC` / `playLeafC` / `AgreesC` と、
  「完成が終状態の開示辺をすべて拡張するなら対局と一致する」
  （`agreesC_of_extends`）。**一致に不変量は不要**なのが要点。
* 不変量 `Inv`（開示頂点の相異なり）の維持と予算勘定（`playC_inv`）。
  新鮮点の存在は `used.length + 2 ≤ N` から。

**BUILD NOTE**: root（`FiniteOrderTM.lean`）非取込。検査は
`lake env lean FiniteOrderTM/TwoPointConcrete.lean`。
-/
import FiniteOrderTM.TwoPointAdversary
import FiniteOrderTM.TwoPointRelabel

namespace PeriodicTM.ClaimA

open Equiv Finset
open PeriodicTM.QueryGame (Tree GoodOutput Runs Valid WinsAt)

variable {N : ℕ}

/-! ### リストの小道具（パスの隣接対 = `zip l l.tail`） -/

section ZipTail

variable {α : Type*}

/-- パスの末尾は辺の始点にならない（`Nodup` のとき）。 -/
theorem getLast_not_source {l : List α} (hnd : l.Nodup) (hne : l ≠ []) :
    ∀ z, (l.getLast hne, z) ∉ l.zip l.tail := by
  induction l with
  | nil => simp at hne
  | cons a t ih =>
    cases t with
    | nil => simp
    | cons b t' =>
      intro z hmem
      simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons] at hmem
      have hlast : (a :: b :: t').getLast (by simp)
          = (b :: t').getLast (by simp) := List.getLast_cons (by simp)
      rcases hmem with heq | hmem
      · -- 先頭辺 (a, b) に一致 ⇒ a = 末尾 ∈ b :: t'、Nodup に矛盾
        have ha : a = (b :: t').getLast (by simp) := by
          have := congrArg Prod.fst heq
          simpa [hlast] using this.symm
        exact (List.nodup_cons.mp hnd).1 (ha ▸ List.getLast_mem _)
      · exact ih (List.nodup_cons.mp hnd).2 (by simp) z (by
          rw [hlast] at hmem
          simpa using hmem)

/-- 辺集合はパスの延長で単調（任意の接尾辞）。 -/
theorem mem_zip_tail_append {l m : List α} {p : α × α}
    (h : p ∈ l.zip l.tail) : p ∈ (l ++ m).zip ((l ++ m).tail) := by
  induction l with
  | nil => simp at h
  | cons a t ih =>
    cases t with
    | nil => simp at h
    | cons b t' =>
      simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons] at h
      rcases h with rfl | h
      · simp [List.cons_append]
      · have := ih (by simpa using h)
        simp only [List.cons_append, List.tail_cons, List.zip_cons_cons,
          List.mem_cons]
        right
        simpa [List.cons_append] using this

/-- パスを 1 点延長すると、末尾からの新しい辺が現れる。 -/
theorem getLast_mem_zip_append {l : List α} (hne : l ≠ []) (y : α) :
    (l.getLast hne, y) ∈ (l ++ [y]).zip ((l ++ [y]).tail) := by
  induction l with
  | nil => simp at hne
  | cons a t ih =>
    cases t with
    | nil => simp
    | cons b t' =>
      have hlast : (a :: b :: t').getLast (by simp)
          = (b :: t').getLast (by simp) := List.getLast_cons (by simp)
      rw [hlast]
      simp only [List.cons_append, List.tail_cons, List.zip_cons_cons,
        List.mem_cons]
      right
      have := ih (by simp)
      simpa [List.cons_append] using this

/-- 第 `i` 要素を 1 点延長したリスト族の平坦化は、元の平坦化に
その点を加えたものの並べ替え。 -/
theorem flatten_set_perm :
    ∀ (L : List (List α)) (i : ℕ) (y : α) (hi : i < L.length),
      (L.set i (L[i]'hi ++ [y])).flatten.Perm (y :: L.flatten)
  | l :: L, 0, y, _ => by
    simp only [List.set_cons_zero, List.flatten_cons, List.getElem_cons_zero,
      List.append_assoc]
    exact List.perm_middle
  | l :: L, i + 1, y, hi => by
    have hi' : i < L.length := by simpa using hi
    simp only [List.set_cons_succ, List.flatten_cons, List.getElem_cons_succ]
    exact ((flatten_set_perm L i y hi').append_left l).trans List.perm_middle

/-- 第 `k` 要素の延長は、各要素を（高々）接尾辞の付加でしか変えない。 -/
theorem mem_set_append :
    ∀ (L : List (List α)) (k : ℕ) (hk : k < L.length) (y : α),
      ∀ l ∈ L, ∃ m, l ++ m ∈ L.set k (L[k]'hk ++ [y])
  | a :: L, 0, _, y, l, hl => by
    rcases List.mem_cons.mp hl with rfl | hl'
    · exact ⟨[y], List.mem_cons.mpr (Or.inl rfl)⟩
    · exact ⟨[], by
        simp only [List.append_nil, List.set_cons_zero]
        exact List.mem_cons.mpr (Or.inr hl')⟩
  | a :: L, k + 1, hk, y, l, hl => by
    rcases List.mem_cons.mp hl with rfl | hl'
    · exact ⟨[], by
        simp only [List.append_nil, List.set_cons_succ]
        exact List.mem_cons.mpr (Or.inl rfl)⟩
    · obtain ⟨m, hm⟩ := mem_set_append L k (by simpa using hk) y l hl'
      exact ⟨m, by
        simp only [List.set_cons_succ]
        exact List.mem_cons.mpr (Or.inr (by simpa using hm))⟩

/-- 空でないパスの点は、末尾であるか、記録済みの後続を持つ。 -/
theorem mem_last_or_source {l : List α} {x : α} (hx : x ∈ l) (hne : l ≠ []) :
    x = l.getLast hne ∨ ∃ z, (x, z) ∈ l.zip l.tail := by
  induction l with
  | nil => simp at hx
  | cons a t ih =>
    cases t with
    | nil =>
      simp only [List.mem_singleton] at hx
      exact Or.inl (by simp [hx])
    | cons b t' =>
      have hlast : (a :: b :: t').getLast (by simp)
          = (b :: t').getLast (by simp) := List.getLast_cons (by simp)
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact Or.inr ⟨b, by simp⟩
      · rcases ih hx' (by simp) with h | ⟨z, hz⟩
        · exact Or.inl (by rw [hlast]; exact h)
        · exact Or.inr ⟨z, by
            simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons]
            exact Or.inr hz⟩

/-- `List.set` と `map` の交換（mathlib に見つからないので用意）。 -/
theorem map_set {β : Type*} (f : α → β) :
    ∀ (l : List α) (i : ℕ) (a : α),
      (l.set i a).map f = (l.map f).set i (f a)
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | x :: t, i + 1, a => by
    simp only [List.set_cons_succ, List.map_cons, map_set f t i a]

end ZipTail

/-! ### 具体状態 -/

/-- 新鮮応答敵対者の具体状態: 0-パスの新頂点列 `p0`、1-パスの `p1`、
迷いパスの列（開始点と後続頂点列）。 -/
structure ConcState (N : ℕ) where
  p0 : List (Fin N)
  p1 : List (Fin N)
  strays : List (Fin N × List (Fin N))

/-- `x` を末端に持つ迷いパスの番号を先頭から探す。 -/
def strayEndScan (x : Fin N) : List (Fin N × List (Fin N)) → Option ℕ
  | [] => none
  | s :: rest =>
    if (s.1 :: s.2).getLast (List.cons_ne_nil _ _) = x then some 0
    else (strayEndScan x rest).map (· + 1)

/-- `strayEndScan` の仕様（見つかった側）。 -/
theorem strayEndScan_spec {x : Fin N} :
    ∀ {L : List (Fin N × List (Fin N))} {i : ℕ}, strayEndScan x L = some i →
      ∃ hi : i < L.length,
        (L[i].1 :: L[i].2).getLast (List.cons_ne_nil _ _) = x := by
  intro L
  induction L with
  | nil => intro i h; simp [strayEndScan] at h
  | cons s rest ih =>
    intro i h
    unfold strayEndScan at h
    by_cases hs : (s.1 :: s.2).getLast (List.cons_ne_nil _ _) = x
    · rw [if_pos hs] at h
      obtain rfl : i = 0 := by simpa using h.symm
      exact ⟨by simp, hs⟩
    · rw [if_neg hs] at h
      obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hjlen, hjlast⟩ := ih hj
      exact ⟨by simpa using hjlen, by simpa using hjlast⟩

/-- `strayEndScan` の仕様（見つからなかった側）。 -/
theorem strayEndScan_none {x : Fin N} :
    ∀ {L : List (Fin N × List (Fin N))}, strayEndScan x L = none →
      ∀ s ∈ L, (s.1 :: s.2).getLast (List.cons_ne_nil _ _) ≠ x := by
  intro L
  induction L with
  | nil => intro _ s hs; simp at hs
  | cons t rest ih =>
    intro h s hs
    unfold strayEndScan at h
    by_cases ht : (t.1 :: t.2).getLast (List.cons_ne_nil _ _) = x
    · rw [if_pos ht] at h
      exact absurd h (by simp)
    · rw [if_neg ht] at h
      rcases List.mem_cons.mp hs with rfl | hs'
      · exact ht
      · exact ih (by simpa using h) s hs'

namespace ConcState

/-- 抽象化: 辺数だけを数える。 -/
def toAdv (C : ConcState N) : AdvState :=
  ⟨C.p0.length, C.p1.length, C.strays.map fun s => s.2.length⟩

/-- `x` を末端に持つ迷いパスの番号（あれば）。 -/
def strayEndIdx (C : ConcState N) (x : Fin N) : Option ℕ :=
  strayEndScan x C.strays

/-- 初期状態（何も開示されていない）。 -/
def init (N : ℕ) : ConcState N := ⟨[], [], []⟩

variable [NeZero N]

/-- 開示済みパスの一覧（0-パス・1-パス・迷いパスの順）。 -/
def paths (C : ConcState N) : List (List (Fin N)) :=
  ((0 : Fin N) :: C.p0) :: ((1 : Fin N) :: C.p1) ::
    (C.strays.map fun s => s.1 :: s.2)

/-- 開示済み頂点（グループ順: 0-パス、1-パス、迷いパス）。 -/
def used (C : ConcState N) : List (Fin N) := C.paths.flatten

/-- 開示済み辺: 各パスの隣接対。 -/
def edges (C : ConcState N) : List (Fin N × Fin N) :=
  (C.paths.map fun l => l.zip l.tail).flatten

/-- 不変量: 開示頂点はすべて相異なり、迷いパスは空でない。 -/
def Inv (C : ConcState N) : Prop :=
  C.used.Nodup ∧ ∀ s ∈ C.strays, s.2 ≠ []

/-- 0-パスの末端。 -/
def end0 (C : ConcState N) : Fin N :=
  ((0 : Fin N) :: C.p0).getLast (List.cons_ne_nil _ _)

/-- 1-パスの末端。 -/
def end1 (C : ConcState N) : Fin N :=
  ((1 : Fin N) :: C.p1).getLast (List.cons_ne_nil _ _)

/-- 未使用の点（クエリ点 `x` も避ける）。存在しなければダミー 0。 -/
def freshPt (C : ConcState N) (x : Fin N) : Fin N :=
  if h : (Finset.univ \ insert x C.used.toFinset).Nonempty
  then (Finset.univ \ insert x C.used.toFinset).min' h
  else 0

/-- 敵対者の答え: 記録済みの後続があればそれ、なければ未使用点。 -/
def answer (C : ConcState N) (x : Fin N) : Fin N :=
  match C.edges.find? (fun p => p.1 == x) with
  | some p => p.2
  | none => C.freshPt x

/-- 0-パスを 1 点延長する。 -/
def extend0 (C : ConcState N) (y : Fin N) : ConcState N :=
  ⟨C.p0 ++ [y], C.p1, C.strays⟩

/-- 1-パスを 1 点延長する。 -/
def extend1 (C : ConcState N) (y : Fin N) : ConcState N :=
  ⟨C.p0, C.p1 ++ [y], C.strays⟩

/-- 迷いパス `i` を 1 点延長する（範囲外なら何もしない）。 -/
def extendStray (C : ConcState N) (i : ℕ) (y : Fin N) : ConcState N :=
  ⟨C.p0, C.p1,
    match C.strays[i]? with
    | some s => C.strays.set i (s.1, s.2 ++ [y])
    | none => C.strays⟩

/-- 新しい迷いパス `x → y` を作る。 -/
def newStray (C : ConcState N) (x y : Fin N) : ConcState N :=
  ⟨C.p0, C.p1, (x, [y]) :: C.strays⟩

/-- 1 手の状態遷移。 -/
def step (C : ConcState N) (x : Fin N) : ConcState N :=
  if x = C.end0 then C.extend0 (C.answer x)
  else if x = C.end1 then C.extend1 (C.answer x)
  else
    match C.strayEndIdx x with
    | some i => C.extendStray i (C.answer x)
    | none =>
        if (C.edges.find? (fun p => p.1 == x)).isSome then C
        else C.newStray x (C.answer x)

/-- 1 手のクエリ種別（`AdvState.step` との可換性のため）。 -/
def kind (C : ConcState N) (x : Fin N) : QueryKind :=
  if x = C.end0 then .extendP0
  else if x = C.end1 then .extendP1
  else
    match C.strayEndIdx x with
    | some i => .extendStray i
    | none =>
        if (C.edges.find? (fun p => p.1 == x)).isSome then .stale else .fresh

end ConcState

/-! ### 分岐の集約（`step`・`kind` の場合分けを 1 回で済ませる） -/

section StepCases

variable [NeZero N]

/-- `strayEndIdx = some i` の仕様: `i` 番の迷いパスの末端が `x`。 -/
theorem strayEndIdx_spec (C : ConcState N) {x : Fin N} {i : ℕ}
    (h : C.strayEndIdx x = some i) :
    ∃ hi : i < C.strays.length,
      (C.strays[i].1 :: C.strays[i].2).getLast (List.cons_ne_nil _ _) = x :=
  strayEndScan_spec h

/-- `strayEndIdx = none` の仕様: どの迷いパスの末端も `x` でない。 -/
theorem strayEndIdx_none (C : ConcState N) {x : Fin N}
    (h : C.strayEndIdx x = none) :
    ∀ s ∈ C.strays,
      (s.1 :: s.2).getLast (List.cons_ne_nil _ _) ≠ x :=
  strayEndScan_none h

/-- **分岐の場合分け**: `step`・`kind` の値は 5 通りのどれか。
以後の証明はすべてこの補題で分岐し、`if`/`match` には触れない。 -/
theorem step_eq (C : ConcState N) (x : Fin N) :
    (x = C.end0 ∧ C.kind x = .extendP0 ∧
      C.step x = C.extend0 (C.answer x)) ∨
    (x ≠ C.end0 ∧ x = C.end1 ∧ C.kind x = .extendP1 ∧
      C.step x = C.extend1 (C.answer x)) ∨
    (∃ i, x ≠ C.end0 ∧ x ≠ C.end1 ∧ C.strayEndIdx x = some i ∧
      C.kind x = .extendStray i ∧ C.step x = C.extendStray i (C.answer x)) ∨
    (x ≠ C.end0 ∧ x ≠ C.end1 ∧ C.strayEndIdx x = none ∧
      (C.edges.find? (fun p => p.1 == x)).isSome ∧ C.kind x = .stale ∧
      C.step x = C) ∨
    (x ≠ C.end0 ∧ x ≠ C.end1 ∧ C.strayEndIdx x = none ∧
      C.edges.find? (fun p => p.1 == x) = none ∧ C.kind x = .fresh ∧
      C.step x = C.newStray x (C.answer x)) := by
  by_cases h0 : x = C.end0
  · refine Or.inl ⟨h0, ?_, ?_⟩ <;>
      simp only [ConcState.kind, ConcState.step, if_pos h0]
  · by_cases h1 : x = C.end1
    · refine Or.inr (Or.inl ⟨h0, h1, ?_, ?_⟩) <;>
        simp only [ConcState.kind, ConcState.step, if_neg h0, if_pos h1]
    · cases hidx : C.strayEndIdx x with
      | some i =>
        refine Or.inr (Or.inr (Or.inl ⟨i, h0, h1, rfl, ?_, ?_⟩)) <;>
          simp only [ConcState.kind, ConcState.step, if_neg h0, if_neg h1,
            hidx]
      | none =>
        by_cases hst : (C.edges.find? (fun p => p.1 == x)).isSome
        · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨h0, h1, rfl, hst, ?_, ?_⟩)))
            <;> simp only [ConcState.kind, ConcState.step, if_neg h0,
              if_neg h1, hidx, if_pos hst]
        · have hst' : C.edges.find? (fun p => p.1 == x) = none :=
            Option.not_isSome_iff_eq_none.mp hst
          refine Or.inr (Or.inr (Or.inr (Or.inr ⟨h0, h1, rfl, hst', ?_, ?_⟩)))
            <;> simp only [ConcState.kind, ConcState.step, if_neg h0,
              if_neg h1, hidx, if_neg hst]

end StepCases

/-! ### 各分岐のパス形状 -/

section PathShapes

variable [NeZero N]

theorem paths_length (C : ConcState N) :
    C.paths.length = C.strays.length + 2 := by
  simp [ConcState.paths]

theorem extend0_paths (C : ConcState N) (y : Fin N) :
    (C.extend0 y).paths
      = C.paths.set 0 (C.paths[0]'(by simp [paths_length]) ++ [y]) := by
  simp [ConcState.extend0, ConcState.paths, List.cons_append]

theorem extend1_paths (C : ConcState N) (y : Fin N) :
    (C.extend1 y).paths
      = C.paths.set 1 (C.paths[1]'(by simp [paths_length]) ++ [y]) := by
  simp [ConcState.extend1, ConcState.paths, List.cons_append]

theorem extendStray_paths (C : ConcState N) (i : ℕ) (y : Fin N)
    (hi : i < C.strays.length) :
    (C.extendStray i y).paths
      = C.paths.set (i + 2)
          (C.paths[i + 2]'(by simp [paths_length]; omega) ++ [y]) := by
  unfold ConcState.extendStray
  rw [List.getElem?_eq_getElem hi]
  simp only [ConcState.paths, List.set_cons_succ, List.getElem_cons_succ,
    map_set, List.getElem_map, List.cons_append]

theorem newStray_paths (C : ConcState N) (x y : Fin N) :
    (C.newStray x y).paths
      = ((0 : Fin N) :: C.p0) :: ((1 : Fin N) :: C.p1) ::
          ((x :: [y]) :: (C.strays.map fun s => s.1 :: s.2)) := by
  simp [ConcState.newStray, ConcState.paths]

/-- 分節の隣接対は辺集合の要素。 -/
theorem edges_mem_of_seg (C : ConcState N) {l : List (Fin N)}
    (hl : l ∈ C.paths) {p : Fin N × Fin N} (hp : p ∈ l.zip l.tail) :
    p ∈ C.edges := by
  simp only [ConcState.edges, List.mem_flatten, List.mem_map]
  exact ⟨_, ⟨l, hl, rfl⟩, hp⟩

end PathShapes

/-! ### 抽象化の可換性と長さ勘定 -/

section Abstraction

variable [NeZero N]

/-- 補助: 各パスの長さの総和。 -/
theorem sum_map_cons_length {α : Type*} (l : List (α × List α)) :
    (l.map fun s => s.2.length + 1).sum
      = l.length + (l.map fun s => s.2.length).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    omega

/-- 開示頂点数 = 抽象状態の `vertexCount`。 -/
theorem used_length (C : ConcState N) :
    C.used.length = C.toAdv.vertexCount := by
  rw [ConcState.used, List.length_flatten]
  simp only [ConcState.paths, List.map_cons, List.sum_cons, List.length_cons,
    List.map_map]
  have h : (C.strays.map (List.length ∘ fun s => s.1 :: s.2)).sum
      = C.strays.length + (C.strays.map fun s => s.2.length).sum := by
    have := sum_map_cons_length C.strays
    simpa [Function.comp_def] using this
  rw [h]
  simp only [ConcState.toAdv, AdvState.vertexCount, List.length_map]
  omega

/-- **抽象化は遷移と可換**: 具体で 1 手進めた状態の抽象化は、
抽象状態を対応する種別で 1 手進めたもの。 -/
theorem toAdv_step (C : ConcState N) (x : Fin N) :
    (C.step x).toAdv = C.toAdv.step (C.kind x) := by
  rcases step_eq C x with ⟨_, hk, hs⟩ | ⟨_, _, hk, hs⟩ |
    ⟨i, _, _, hidx, hk, hs⟩ | ⟨_, _, _, _, hk, hs⟩ | ⟨_, _, _, _, hk, hs⟩
  · rw [hk, hs]
    simp [ConcState.extend0, ConcState.toAdv, AdvState.step]
  · rw [hk, hs]
    simp [ConcState.extend1, ConcState.toAdv, AdvState.step]
  · rw [hk, hs]
    obtain ⟨hi, -⟩ := strayEndIdx_spec C hidx
    unfold ConcState.extendStray
    rw [List.getElem?_eq_getElem hi]
    simp only [ConcState.toAdv, AdvState.step, AdvState.mk.injEq, true_and]
    rw [map_set]
    congr 1
    rw [List.getElem?_map, List.getElem?_eq_getElem hi]
    simp
  · rw [hk, hs]
    simp [ConcState.toAdv, AdvState.step]
  · rw [hk, hs]
    simp [ConcState.newStray, ConcState.toAdv, AdvState.step]

end Abstraction

/-! ### 敵対者の答えと辺の関係 -/

section Answer

variable [NeZero N]

/-- `find?` が見つけた対は辺集合の要素で、始点は `x`。 -/
theorem find?_edge {C : ConcState N} {x : Fin N} {p : Fin N × Fin N}
    (h : C.edges.find? (fun p => p.1 == x) = some p) :
    p ∈ C.edges ∧ p.1 = x := by
  refine ⟨List.mem_of_find?_eq_some h, ?_⟩
  have := List.find?_some h
  simpa using this

/-- 記録済みの後続がある場合、答えの辺はすでに辺集合にある。 -/
theorem answer_edge_of_stale {C : ConcState N} {x : Fin N}
    (h : (C.edges.find? (fun p => p.1 == x)).isSome) :
    (x, C.answer x) ∈ C.edges := by
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨hmem, hfst⟩ := find?_edge hp
  have hans : C.answer x = p.2 := by
    unfold ConcState.answer
    rw [hp]
  rw [hans, ← hfst]
  exact hmem

/-- **各パスは遷移で延長されるだけ**（接尾辞の付加）。 -/
theorem step_paths_extend (C : ConcState N) (x : Fin N) :
    ∀ l ∈ C.paths, ∃ m, l ++ m ∈ (C.step x).paths := by
  intro l hl
  rcases step_eq C x with ⟨_, _, hs⟩ | ⟨_, _, _, hs⟩ |
    ⟨i, _, _, hidx, _, hs⟩ | ⟨_, _, _, _, _, hs⟩ | ⟨_, _, _, _, _, hs⟩
  · rw [hs, extend0_paths]
    exact mem_set_append C.paths 0 (by simp [paths_length]) _ l hl
  · rw [hs, extend1_paths]
    exact mem_set_append C.paths 1 (by simp [paths_length]) _ l hl
  · obtain ⟨hi, -⟩ := strayEndIdx_spec C hidx
    rw [hs, extendStray_paths C i _ hi]
    exact mem_set_append C.paths (i + 2) (by simp [paths_length]; omega) _ l hl
  · exact ⟨[], by rw [hs]; simpa using hl⟩
  · refine ⟨[], ?_⟩
    rw [hs, newStray_paths]
    simp only [List.append_nil]
    rcases List.mem_cons.mp hl with rfl | hl'
    · exact List.mem_cons.mpr (Or.inl rfl)
    · rcases List.mem_cons.mp hl' with rfl | hl''
      · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
      · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr
          (List.mem_cons.mpr (Or.inr hl'')))))

/-- **辺集合は遷移で単調**。 -/
theorem edges_mono_step (C : ConcState N) (x : Fin N) {p : Fin N × Fin N}
    (hp : p ∈ C.edges) : p ∈ (C.step x).edges := by
  simp only [ConcState.edges, List.mem_flatten, List.mem_map] at hp
  obtain ⟨_, ⟨l, hl, rfl⟩, hpl⟩ := hp
  obtain ⟨m, hm⟩ := step_paths_extend C x l hl
  exact edges_mem_of_seg _ hm (mem_zip_tail_append hpl)

/-- **答えの辺は遷移後の辺集合にある**（不変量は不要）。 -/
theorem answer_edge_mem (C : ConcState N) (x : Fin N) :
    (x, C.answer x) ∈ (C.step x).edges := by
  rcases step_eq C x with ⟨h0, _, hs⟩ | ⟨_, h1, _, hs⟩ |
    ⟨i, _, _, hidx, _, hs⟩ | ⟨_, _, _, hst, _, hs⟩ | ⟨_, _, _, hst, _, hs⟩
  · subst h0
    rw [hs]
    refine edges_mem_of_seg _ (l := ((0 : Fin N) :: C.p0) ++ [C.answer C.end0])
      ?_ ?_
    · simp [ConcState.extend0, ConcState.paths, List.cons_append]
    · exact getLast_mem_zip_append (List.cons_ne_nil _ _) _
  · subst h1
    rw [hs]
    refine edges_mem_of_seg _ (l := ((1 : Fin N) :: C.p1) ++ [C.answer C.end1])
      ?_ ?_
    · simp [ConcState.extend1, ConcState.paths, List.cons_append]
    · exact getLast_mem_zip_append (List.cons_ne_nil _ _) _
  · obtain ⟨hi, hlast⟩ := strayEndIdx_spec C hidx
    rw [hs]
    refine edges_mem_of_seg _
      (l := (C.strays[i].1 :: C.strays[i].2) ++ [C.answer x]) ?_ ?_
    · rw [extendStray_paths C i _ hi]
      have hset : i + 2 < (C.paths.set (i + 2)
          (C.paths[i + 2]'(by simp [paths_length]; omega)
            ++ [C.answer x])).length := by
        simp [paths_length]
        omega
      have hval : (C.paths.set (i + 2)
          (C.paths[i + 2]'(by simp [paths_length]; omega)
            ++ [C.answer x]))[i + 2]'hset
          = (C.strays[i].1 :: C.strays[i].2) ++ [C.answer x] := by
        rw [List.getElem_set_self]
        congr 1
        show C.paths[i + 2]'_ = _
        simp [ConcState.paths]
      exact hval ▸ List.getElem_mem _
    · rw [← hlast]
      exact getLast_mem_zip_append (List.cons_ne_nil _ _) _
  · rw [hs]
    exact answer_edge_of_stale hst
  · rw [hs]
    refine edges_mem_of_seg _ (l := x :: [C.answer x]) ?_ ?_
    · rw [newStray_paths]
      exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr
        (List.mem_cons.mpr (Or.inl rfl)))))
    · simp

end Answer

/-! ### 不変量の維持 -/

section Invariant

variable [NeZero N]

/-- 未使用点の仕様: 余白があれば、`freshPt` は使用済みでも `x` でもない。 -/
theorem freshPt_spec (C : ConcState N) (x : Fin N)
    (h : C.used.length + 2 ≤ N) :
    C.freshPt x ∉ C.used ∧ C.freshPt x ≠ x := by
  have hcard : (insert x C.used.toFinset).card < N := by
    calc (insert x C.used.toFinset).card
        ≤ C.used.toFinset.card + 1 := Finset.card_insert_le _ _
      _ ≤ C.used.length + 1 := by
          have := C.used.toFinset_card_le
          omega
      _ < N := by omega
  have hne : (Finset.univ \ insert x C.used.toFinset).Nonempty := by
    rw [Finset.sdiff_nonempty]
    intro hsub
    have hN := Finset.card_le_card hsub
    rw [Finset.card_univ, Fintype.card_fin] at hN
    omega
  have hmem := Finset.min'_mem _ hne
  rw [Finset.mem_sdiff, Finset.mem_insert, not_or] at hmem
  unfold ConcState.freshPt
  rw [dif_pos hne]
  exact ⟨fun hmem' => hmem.2.2 (List.mem_toFinset.mpr hmem'), hmem.2.1⟩

/-- パスは互いに素（`Inv` から）: 異なる（値の）パスは点を共有しない。 -/
theorem paths_disjoint (C : ConcState N) (hInv : C.Inv) :
    ∀ l ∈ C.paths, ∀ l' ∈ C.paths, l ≠ l' → List.Disjoint l l' := by
  have hnd := (List.nodup_flatten.mp hInv.1).2
  intro l hl l' hl' hne
  exact hnd.forall (fun _ _ h => h.symm) hl hl' hne

/-- 各パスは Nodup（`Inv` から）。 -/
theorem paths_nodup (C : ConcState N) (hInv : C.Inv) :
    ∀ l ∈ C.paths, l.Nodup :=
  (List.nodup_flatten.mp hInv.1).1

/-- **末端は辺の始点にならない**: `Inv` のもとで、どのパスの末端からも
記録済みの辺は出ていない。 -/
theorem not_source_of_getLast (C : ConcState N) (hInv : C.Inv)
    {l : List (Fin N)} (hl : l ∈ C.paths) (hne : l ≠ []) :
    ∀ z, (l.getLast hne, z) ∉ C.edges := by
  intro z hmem
  simp only [ConcState.edges, List.mem_flatten, List.mem_map] at hmem
  obtain ⟨_, ⟨l', hl', rfl⟩, hzip⟩ := hmem
  by_cases heq : l = l'
  · subst heq
    exact getLast_not_source (paths_nodup C hInv l hl) hne z hzip
  · have hx : l.getLast hne ∈ l' := (List.of_mem_zip hzip).1
    exact paths_disjoint C hInv l hl l' hl' heq (List.getLast_mem hne) hx

/-- 0-パスの末端が使われているパスは 0-パスに限る（`Inv` 下の帰結として、
末端クエリでは記録済みの後続はない）。 -/
theorem find?_eq_none_of_end (C : ConcState N) (hInv : C.Inv) {x : Fin N}
    (h : x = C.end0 ∨ x = C.end1 ∨ ∃ i, C.strayEndIdx x = some i) :
    C.edges.find? (fun p => p.1 == x) = none := by
  rw [List.find?_eq_none]
  rintro ⟨u, v⟩ hp hbeq
  have hux : u = x := by simpa using hbeq
  subst hux
  rcases h with h0 | h1 | ⟨i, hi⟩
  · subst h0
    exact not_source_of_getLast C hInv (l := (0 : Fin N) :: C.p0)
      (List.mem_cons.mpr (Or.inl rfl)) (List.cons_ne_nil _ _) v hp
  · subst h1
    exact not_source_of_getLast C hInv (l := (1 : Fin N) :: C.p1)
      (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
      (List.cons_ne_nil _ _) v hp
  · obtain ⟨hilen, hilast⟩ := strayEndIdx_spec C hi
    have hlmem : C.strays[i].1 :: C.strays[i].2 ∈ C.paths := by
      refine List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr ?_)))
      exact List.mem_map.mpr ⟨_, List.getElem_mem _, rfl⟩
    have := not_source_of_getLast C hInv hlmem (List.cons_ne_nil _ _) v
    rw [hilast] at this
    exact this hp

/-- 新鮮クエリの点は未使用（`Inv` 下）。 -/
theorem not_used_of_fresh (C : ConcState N) (hInv : C.Inv) {x : Fin N}
    (h0 : x ≠ C.end0) (h1 : x ≠ C.end1)
    (hidx : C.strayEndIdx x = none)
    (hst : C.edges.find? (fun p => p.1 == x) = none) :
    x ∉ C.used := by
  intro hx
  simp only [ConcState.used, List.mem_flatten] at hx
  obtain ⟨l, hl, hxl⟩ := hx
  have hlne : l ≠ [] := by
    rintro rfl
    simp at hxl
  rcases mem_last_or_source hxl hlne with hlast | ⟨z, hz⟩
  · -- x はどれかのパスの末端 ⇒ 3 分類のどれかに矛盾
    rcases List.mem_cons.mp hl with rfl | hl'
    · exact h0 (by rw [hlast]; rfl)
    · rcases List.mem_cons.mp hl' with rfl | hl''
      · exact h1 (by rw [hlast]; rfl)
      · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hl''
        exact strayEndIdx_none C hidx s hs (by rw [← hlast])
  · -- x は後続を持つ ⇒ find? = none に矛盾
    have hmem : (x, z) ∈ C.edges := edges_mem_of_seg C hl hz
    rw [List.find?_eq_none] at hst
    exact hst _ hmem (by simp)

/-- 末端クエリの答えは未使用点。 -/
theorem answer_eq_fresh_of_end (C : ConcState N) (hInv : C.Inv) {x : Fin N}
    (h : x = C.end0 ∨ x = C.end1 ∨ ∃ i, C.strayEndIdx x = some i) :
    C.answer x = C.freshPt x := by
  unfold ConcState.answer
  rw [find?_eq_none_of_end C hInv h]

/-- **1 手の使用リストの変化**: 並べ替えの意味で「未使用点 1 つ追加」
（延長）か「クエリ点と未使用点を追加」（新迷い）か「変化なし」
（既知の答え）のいずれか。 -/
theorem used_step_perm (C : ConcState N) (x : Fin N) (hInv : C.Inv) :
    (C.step x).used.Perm (C.freshPt x :: C.used) ∨
    ((C.step x).used.Perm (C.freshPt x :: x :: C.used) ∧ x ∉ C.used) ∨
    (C.step x).used = C.used := by
  rcases step_eq C x with ⟨h0, _, hs⟩ | ⟨h0, h1, _, hs⟩ |
    ⟨i, h0, h1, hidx, _, hs⟩ | ⟨_, _, _, _, _, hs⟩ | ⟨h0, h1, hidx, hst, _, hs⟩
  · left
    rw [hs, answer_eq_fresh_of_end C hInv (Or.inl h0)]
    rw [ConcState.used, extend0_paths]
    exact flatten_set_perm C.paths 0 _ (by simp [paths_length])
  · left
    rw [hs, answer_eq_fresh_of_end C hInv (Or.inr (Or.inl h1))]
    rw [ConcState.used, extend1_paths]
    exact flatten_set_perm C.paths 1 _ (by simp [paths_length])
  · left
    obtain ⟨hi, -⟩ := strayEndIdx_spec C hidx
    rw [hs, answer_eq_fresh_of_end C hInv (Or.inr (Or.inr ⟨i, hidx⟩))]
    rw [ConcState.used, extendStray_paths C i _ hi]
    exact flatten_set_perm C.paths (i + 2) _ (by simp [paths_length]; omega)
  · right; right
    rw [hs]
  · right; left
    have hans : C.answer x = C.freshPt x := by
      unfold ConcState.answer
      rw [hst]
    refine ⟨?_, not_used_of_fresh C hInv h0 h1 hidx hst⟩
    rw [hs, hans]
    show ((C.newStray x (C.freshPt x)).paths).flatten.Perm _
    rw [newStray_paths]
    simp only [List.flatten_cons]
    -- A ++ (B ++ ((x :: [y]) ++ F)) ~ y :: x :: (A ++ (B ++ F))
    have h1' : (x :: [C.freshPt x]) ++
        (C.strays.map fun s => s.1 :: s.2).flatten
        = x :: C.freshPt x :: (C.strays.map fun s => s.1 :: s.2).flatten :=
      rfl
    rw [h1']
    have hstep1 : (((1 : Fin N) :: C.p1) ++ (x :: C.freshPt x ::
        (C.strays.map fun s => s.1 :: s.2).flatten)).Perm
        (x :: (((1 : Fin N) :: C.p1) ++ (C.freshPt x ::
          (C.strays.map fun s => s.1 :: s.2).flatten))) := List.perm_middle
    have hstep2 : (((1 : Fin N) :: C.p1) ++ (C.freshPt x ::
        (C.strays.map fun s => s.1 :: s.2).flatten)).Perm
        (C.freshPt x :: (((1 : Fin N) :: C.p1) ++
          (C.strays.map fun s => s.1 :: s.2).flatten)) := List.perm_middle
    have hinner : (((1 : Fin N) :: C.p1) ++ (x :: C.freshPt x ::
        (C.strays.map fun s => s.1 :: s.2).flatten)).Perm
        (C.freshPt x :: x :: (((1 : Fin N) :: C.p1) ++
          (C.strays.map fun s => s.1 :: s.2).flatten)) :=
      (hstep1.trans (hstep2.cons x)).trans (List.Perm.swap _ _ _)
    have houter := hinner.append_left ((0 : Fin N) :: C.p0)
    refine houter.trans ?_
    have hstep3 : (((0 : Fin N) :: C.p0) ++ (C.freshPt x :: x ::
        (((1 : Fin N) :: C.p1) ++
          (C.strays.map fun s => s.1 :: s.2).flatten))).Perm
        (C.freshPt x :: (((0 : Fin N) :: C.p0) ++ (x ::
          (((1 : Fin N) :: C.p1) ++
            (C.strays.map fun s => s.1 :: s.2).flatten)))) := List.perm_middle
    have hstep4 : (((0 : Fin N) :: C.p0) ++ (x ::
        (((1 : Fin N) :: C.p1) ++
          (C.strays.map fun s => s.1 :: s.2).flatten))).Perm
        (x :: (((0 : Fin N) :: C.p0) ++
          (((1 : Fin N) :: C.p1) ++
            (C.strays.map fun s => s.1 :: s.2).flatten))) := List.perm_middle
    exact hstep3.trans ((hstep4.cons _))

/-- 迷いパスの非空性は保たれる。 -/
theorem strays_ne_nil_step (C : ConcState N) (x : Fin N)
    (h : ∀ s ∈ C.strays, s.2 ≠ []) :
    ∀ s ∈ (C.step x).strays, s.2 ≠ [] := by
  rcases step_eq C x with ⟨_, _, hs⟩ | ⟨_, _, _, hs⟩ |
    ⟨i, _, _, _, _, hs⟩ | ⟨_, _, _, _, _, hs⟩ | ⟨_, _, _, _, _, hs⟩
  · rw [hs]; exact h
  · rw [hs]; exact h
  · rw [hs]
    unfold ConcState.extendStray
    cases hopt : C.strays[i]? with
    | some s0 =>
      intro s hs'
      rcases List.mem_or_eq_of_mem_set hs' with hs'' | hs''
      · exact h s hs''
      · rw [hs'']
        simp
    | none => exact h
  · rw [hs]; exact h
  · rw [hs]
    intro s hs'
    rcases List.mem_cons.mp hs' with rfl | hs''
    · simp
    · exact h s hs''

/-- **不変量の維持**: 余白があれば 1 手で `Inv` は保たれ、
使用リストは高々 2 伸びる。 -/
theorem inv_step (C : ConcState N) (x : Fin N) (hInv : C.Inv)
    (hroom : C.used.length + 2 ≤ N) :
    (C.step x).Inv ∧ (C.step x).used.length ≤ C.used.length + 2 := by
  obtain ⟨hfresh, hfx⟩ := freshPt_spec C x hroom
  rcases used_step_perm C x hInv with hperm | ⟨hperm, hxused⟩ | heq
  · refine ⟨⟨hperm.nodup_iff.mpr ?_, strays_ne_nil_step C x hInv.2⟩, ?_⟩
    · exact List.nodup_cons.mpr ⟨hfresh, hInv.1⟩
    · rw [hperm.length_eq]
      simp
  · refine ⟨⟨hperm.nodup_iff.mpr ?_, strays_ne_nil_step C x hInv.2⟩, ?_⟩
    · refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨hxused, hInv.1⟩⟩
      simp only [List.mem_cons]
      rintro (heq | hmem)
      · exact hfx heq
      · exact hfresh hmem
    · rw [hperm.length_eq]
      simp
  · refine ⟨⟨?_, strays_ne_nil_step C x hInv.2⟩, ?_⟩
    · show (C.step x).used.Nodup
      rw [heq]
      exact hInv.1
    · show (C.step x).used.length ≤ _
      rw [heq]
      omega

end Invariant

/-! ### 木に沿った具体対局 -/

section Play

variable [NeZero N]

/-- 木を最後まで辿ったときの終状態。 -/
def playC : {q : ℕ} → Tree N q → ConcState N → ConcState N
  | _, .leaf _ _, C => C
  | _, .node x child, C => playC (child (C.answer x)) (C.step x)

/-- 対局が辿り着く葉の出力対。 -/
def playLeafC : {q : ℕ} → Tree N q → ConcState N → Fin N × Fin N
  | _, .leaf v₀ v₁, _ => (v₀, v₁)
  | _, .node x child, C => playLeafC (child (C.answer x)) (C.step x)

/-- 完成 `f` が対局の答えと各手で一致する。 -/
def AgreesC (f : Perm (Fin N)) :
    {q : ℕ} → Tree N q → ConcState N → Prop
  | _, .leaf _ _, _ => True
  | _, .node x child, C =>
      f x = C.answer x ∧ AgreesC f (child (C.answer x)) (C.step x)

/-- 辺集合は対局を通して単調。 -/
theorem playC_edges_mono :
    ∀ {q : ℕ} (t : Tree N q) (C : ConcState N) {p : Fin N × Fin N},
      p ∈ C.edges → p ∈ (playC t C).edges
  | _, .leaf _ _, _, _, hp => hp
  | _, .node x child, C, _, hp =>
      playC_edges_mono (child (C.answer x)) (C.step x)
        (edges_mono_step C x hp)

/-- **一致の十分条件**: 完成が終状態の開示辺をすべて拡張するなら、
対局と各手で一致する。不変量は不要（辺は常に記録されるから）。 -/
theorem agreesC_of_extends (f : Perm (Fin N)) :
    ∀ {q : ℕ} (t : Tree N q) (C : ConcState N),
      (∀ p ∈ (playC t C).edges, f p.1 = p.2) → AgreesC f t C
  | _, .leaf _ _, _, _ => trivial
  | _, .node x child, C, hext => by
    refine ⟨?_, agreesC_of_extends f (child (C.answer x)) (C.step x) hext⟩
    have hedge : (x, C.answer x)
        ∈ (playC (child (C.answer x)) (C.step x)).edges :=
      playC_edges_mono (child (C.answer x)) (C.step x) (answer_edge_mem C x)
    exact hext _ hedge

/-- **一致すれば同じ葉に着く**（`runs_iff_goodOutput_playLeaf` の具体版）。 -/
theorem runsC_iff_goodOutput (a b : Fin N) (f : Perm (Fin N)) :
    ∀ {q : ℕ} (t : Tree N q) (C : ConcState N), AgreesC f t C →
      (Runs a b t f ↔ GoodOutput a b f (playLeafC t C).1 (playLeafC t C).2)
  | _, .leaf v₀ v₁, C, _ => Iff.rfl
  | _, .node x child, C, h => by
    obtain ⟨hx, hrest⟩ := h
    show Runs a b (child (f x)) f ↔ _
    rw [hx]
    exact runsC_iff_goodOutput a b f (child (C.answer x)) (C.step x) hrest

/-- **木が勝てないことの十分条件**(具体版)。 -/
theorem not_winsAt_of_bad_leafC {n ℓ : ℕ} (a b : Fin N) {q : ℕ}
    (t : Tree N q) (C : ConcState N) (f : Perm (Fin N))
    (hvalid : Valid n ℓ a f) (hagree : AgreesC f t C)
    (hbad : ¬ GoodOutput a b f (playLeafC t C).1 (playLeafC t C).2) :
    ¬ WinsAt n ℓ a b t := by
  intro hwin
  exact hbad ((runsC_iff_goodOutput a b f t C hagree).mp (hwin f hvalid))

/-- 抽象化された終状態の予算勘定: 深さ `q` の木で `q` は高々 `q` 増える。 -/
theorem playC_toAdv_q :
    ∀ {q : ℕ} (t : Tree N q) (C : ConcState N),
      (playC t C).toAdv.q ≤ C.toAdv.q + q
  | _, .leaf _ _, _ => Nat.le_refl _
  | _, .node x child, C => by
    have h1 := playC_toAdv_q (child (C.answer x)) (C.step x)
    have h2 : (C.step x).toAdv.q ≤ C.toAdv.q + 1 := by
      rw [toAdv_step]
      exact AdvState.step_q_le _ _
    simp only [playC]
    omega

/-- **対局の主不変量**: 余白 `used + 2q ≤ N` のもとで `Inv` は最後まで
保たれ、使用リストは高々 `2q` 伸びる。 -/
theorem playC_inv :
    ∀ {q : ℕ} (t : Tree N q) (C : ConcState N), C.Inv →
      C.used.length + 2 * q ≤ N →
      (playC t C).Inv ∧ (playC t C).used.length ≤ C.used.length + 2 * q
  | _, .leaf _ _, _, hInv, _ => ⟨hInv, by simp only [playC]; omega⟩
  | _, .node x child, C, hInv, hroom => by
    obtain ⟨hInv', hlen'⟩ := inv_step C x hInv (by omega)
    obtain ⟨hInvF, hlenF⟩ := playC_inv (child (C.answer x)) (C.step x) hInv'
      (by omega)
    simp only [playC]
    exact ⟨hInvF, by omega⟩

/-- 初期状態は不変量を満たす（`N ≥ 2`）。 -/
theorem init_inv (hN : 2 ≤ N) : (ConcState.init N).Inv := by
  constructor
  · have hnd : ([0, 1].map (Fin.ofNat N)).Nodup := by
      refine ofNat_injOn ?_ (by simp)
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · omega
      · rcases List.mem_cons.mp hx' with rfl | hx''
        · omega
        · simp at hx''
    simp only [List.map_cons, List.map_nil, ofNat_zero_eq_zero,
      ofNat_one_eq_one hN] at hnd
    simpa [ConcState.init, ConcState.used, ConcState.paths] using hnd
  · simp [ConcState.init]

/-- 初期状態の使用リストの長さは 2。 -/
theorem init_used_length : (ConcState.init N).used.length = 2 := by
  simp [ConcState.init, ConcState.used, ConcState.paths]

/-- 初期状態の抽象化は空状態。 -/
theorem init_toAdv : (ConcState.init N).toAdv = ⟨0, 0, []⟩ := rfl

end Play

end PeriodicTM.ClaimA

#print axioms PeriodicTM.ClaimA.playC_inv
#print axioms PeriodicTM.ClaimA.agreesC_of_extends
#print axioms PeriodicTM.ClaimA.not_winsAt_of_bad_leafC
#print axioms PeriodicTM.ClaimA.toAdv_step
#print axioms PeriodicTM.ClaimA.used_length
