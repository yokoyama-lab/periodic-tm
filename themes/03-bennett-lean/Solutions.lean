/-
Exercises.lean の模範解答。まず自力で解いてから読むこと。

実行方法（lean/ ディレクトリから）:
  lake env lean ../themes/03-bennett-lean/Solutions.lean
-/
import Mathlib.Logic.Function.Iterate
import Mathlib.Logic.Function.Basic

open Function

variable {α β : Type*}

/-- 演習1: 対合は全単射。単射は f を両辺にかけて 2 回で戻ることを使い、
全射は x = f (f x) が f の像であることを使う。 -/
example (f : α → α) (hf : Involutive f) : Bijective f := by
  constructor
  · intro a b h
    rw [← hf a, ← hf b, h]
  · intro b
    exact ⟨f b, hf b⟩

/-- 演習2: 可換な対合の合成は対合。可換性を 1 点 g x で使い、
g・f の対合性を順に消す。 -/
example (f g : α → α) (hf : Involutive f) (hg : Involutive g)
    (hcomm : f ∘ g = g ∘ f) : Involutive (f ∘ g) := by
  intro x
  have h := congrFun hcomm (g x)
  simp only [comp_apply] at h ⊢
  rw [← h, hg, hf]

/-- 演習3: 左逆の定義そのもの。`hg` の型を `#check` で見よ。 -/
example (f : α → β) (g : β → α) (hg : LeftInverse g f) :
    ∀ x : α, g (f x) = x :=
  fun x => hg x

/-- 演習4: 履歴付き写像は単射。第 1 成分への射影が復元器になる。 -/
example (f : α → β) : Injective (fun x : α => (x, f x)) :=
  fun _ _ h => congrArg Prod.fst h

/-- 演習5: uncompute。演習4の単射性と `Function.leftInverse_invFun` を
組み合わせるだけ。 -/
example [Nonempty α] (f : α → β) :
    ∀ x : α, Function.invFun (fun x : α => (x, f x)) (x, f x) = x :=
  fun x =>
    Function.leftInverse_invFun (fun _ _ h => congrArg Prod.fst h) x
