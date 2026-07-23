/-
Bennett 可逆化に向けた準備演習（易→難）。

実行方法（lean/ ディレクトリから）:
  lake env lean ../themes/03-bennett-lean/Exercises.lean

`sorry` を埋めて警告が消えれば正解。これは演習用ファイルであり、
本体（lake build）のビルド対象には含まれていない。
-/
import Mathlib.Logic.Function.Iterate
import Mathlib.Logic.Function.Basic

open Function

variable {α β : Type*}

/-- 演習1: 対合は全単射である。ヒント: `Function.Involutive.bijective`
を自分で再証明する。`⟨fun a b h => ?_, fun b => ?_⟩` の形から始めよ。 -/
example (f : α → α) (hf : Involutive f) : Bijective f := by
  sorry

/-- 演習2: 対合 f, g が可換なら f ∘ g も対合。 -/
example (f g : α → α) (hf : Involutive f) (hg : Involutive g)
    (hcomm : f ∘ g = g ∘ f) : Involutive (f ∘ g) := by
  sorry

/-- 演習3: 「実行してから逆再生すると元に戻る」の関数版。
f が左逆 g を持つとき、履歴 (x, f x) から x を復元できる。 -/
example (f : α → β) (g : β → α) (hg : LeftInverse g f) :
    ∀ x : α, g (f x) = x := by
  sorry

/-- 演習4: Bennett の核。x ↦ (x, f x) は f が何であれ単射
（可逆化は情報を捨てないことで可逆性を得る）。 -/
example (f : α → β) : Injective (fun x : α => (x, f x)) := by
  sorry

/-- 演習5: uncompute。演習4の単射性から、履歴 (x, f x) を消して x を
復元する写像が存在する（`Function.invFun` と
`Function.leftInverse_invFun` を調べよ）。 -/
example [Nonempty α] (f : α → β) :
    ∀ x : α, Function.invFun (fun x : α => (x, f x)) (x, f x) = x := by
  sorry
