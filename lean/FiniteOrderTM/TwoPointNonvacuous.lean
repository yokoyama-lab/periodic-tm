/-
FiniteOrderTM/TwoPointNonvacuous.lean
— 定理9.6 (`gameValue_eq`) のオラクル約束 `validPerms N ℓ ℓ 0` が
「いつ空でないか」を確定する: `0 < ℓ ≤ N` のとき、かつそのときに限る。

`TwoPointUpper.lean` / `TwoPointLowerBound.lean` の上下界の議論はすべて
「約束を満たす `f` が存在する」ことを暗黙に前提しており、約束が空なら
`gameValue_eq` の主張は空虚に真になる（全称命題は反例なしで成立する）。
この文書は定理9.6 が**実質を持つ範囲**を確定する: `ℓ = 0` や `ℓ > N` では
約束は空、`0 < ℓ ≤ N` では非空（`0` を含む長さ `ℓ` の巡回置換が証拠）。

証拠の構成は `TwoPointClaimAGeneral.lean` の道具をそのまま使う:
`l₁ := (List.range ℓ).map (Fin.ofNat N)`、`l₂ := []` として
`f := l₁.formPerm * ([] : List (Fin N)).formPerm`（`= l₁.formPerm`）。
`orbit_card` が軌道長 `= l₁.length = ℓ` を、`formPerm_pow_eq_one_of_dvd` が
`f ^ ℓ = 1` を直接与える。逆方向は、軌道が `Fin N` の部分 Finset である
ことから `card ≤ N`、および軌道が自分自身 `a` を常に含むことから
`0 < card` が出る、というだけの一般論。

sorry・admit・新規 axiom・`native_decide` は使わない（完全に記号的な一般証明）。

さらに、`TwoPointUpper.lean` の `gameValue_eq`（定理9.6・値の公式）と
上の非空性の特徴づけを合わせ、**定理9.6 のどこに実質があるか**を完全に
確定する（下の「定理9.6：どこに実質があるか」節）: `N < ℓ` の空虚域では
値は理由つきで `0`（`k1Star_eq_zero_of_le` は閉形式そのものが崩壊する
ことを、`gameValue_eq_zero_of_lt` は約束が空だから木が要らないことを、
独立に示す）。`0 < ℓ ≤ N` の非空虚域では、値の公式と「約束は非空」が
同時に成り立つ（`gameValue_eq_nonvacuous`）。 -/
import FiniteOrderTM.QueryGame
import FiniteOrderTM.TwoPointClaimAGeneral
import FiniteOrderTM.TwoPointUpper

namespace PeriodicTM.Nonvacuous

open Equiv Finset
open PeriodicTM.QueryGame

/-! ## 証拠の構成: `0 < ℓ ≤ N` なら約束は非空 -/

/-- **約束を満たす置換の存在**: `0 < ℓ ≤ N` のとき、`0` を含む長さ `ℓ` の
巡回置換 `f`（`{0, 1, …, ℓ-1}` を `Fin.ofNat N` で送った巡回置換）が
`Valid ℓ ℓ 0 f` を満たす。 -/
theorem exists_valid {N ℓ : ℕ} [NeZero N] (hℓ : 0 < ℓ) (hlN : ℓ ≤ N) :
    ∃ f : Perm (Fin N), Valid ℓ ℓ (0 : Fin N) f := by
  set l₁ : List (Fin N) := (List.range ℓ).map (Fin.ofNat N) with hl₁def
  have hlt : ∀ x ∈ List.range ℓ, x < N := by
    intro x hx
    rw [List.mem_range] at hx
    omega
  have hnodup : l₁.Nodup := PeriodicTM.ClaimA.ofNat_injOn hlt (List.nodup_range)
  have hlen : l₁.length = ℓ := by
    simp [hl₁def]
  have hdisj : List.Disjoint l₁ ([] : List (Fin N)) := by
    intro x _ hx'
    exact absurd hx' (List.not_mem_nil)
  have hmem0 : (0 : Fin N) ∈ l₁ := by
    rw [hl₁def, List.mem_map]
    refine ⟨0, ?_, PeriodicTM.ClaimA.ofNat_zero_eq_zero⟩
    rw [List.mem_range]
    exact hℓ
  refine ⟨l₁.formPerm * ([] : List (Fin N)).formPerm, ?_, ?_⟩
  · have heq : l₁.formPerm * ([] : List (Fin N)).formPerm = l₁.formPerm := by
      rw [List.formPerm_nil, mul_one]
    rw [heq]
    exact PeriodicTM.ClaimA.formPerm_pow_eq_one_of_dvd hnodup (hlen ▸ dvd_refl ℓ)
  · have := PeriodicTM.ClaimA.orbit_card hnodup hdisj hmem0
    rwa [hlen] at this

/-! ## 逆向き: 約束が満たされるなら `0 < ℓ ≤ N` -/

/-- **約束は `N` を超えない**: 軌道は `Fin N` の部分 Finset なので、
その濃度 `ℓ` は `N` 以下。 -/
theorem le_of_valid {N ℓ : ℕ} {a : Fin N} {f : Perm (Fin N)} (h : Valid ℓ ℓ a f) :
    ℓ ≤ N := by
  have hcard : #({y | f.SameCycle a y} : Finset (Fin N)) ≤ Fintype.card (Fin N) :=
    Finset.card_le_univ _
  rw [h.2, Fintype.card_fin] at hcard
  exact hcard

/-- **約束は必ず正**: 軌道は常に `a` 自身を含むので空になれない。 -/
theorem pos_of_valid {N ℓ : ℕ} {a : Fin N} {f : Perm (Fin N)} (h : Valid ℓ ℓ a f) :
    0 < ℓ := by
  have hmem : a ∈ ({y | f.SameCycle a y} : Finset (Fin N)) := by
    simp [Perm.SameCycle.refl f a]
  have hpos : 0 < #({y | f.SameCycle a y} : Finset (Fin N)) :=
    Finset.card_pos.mpr ⟨a, hmem⟩
  rwa [h.2] at hpos

/-! ## まとめ: 約束の非空性の完全な特徴づけ -/

/-- **定理9.6 が実質を持つ範囲**: 約束 `validPerms N ℓ ℓ 0` が非空である
ことは、ちょうど `0 < ℓ ≤ N` と同値。`ℓ = 0` や `ℓ > N` では
`gameValue_eq` は空虚に真になるだけで、内容を持たない。 -/
theorem validPerms_nonempty_iff {N ℓ : ℕ} [NeZero N] :
    (validPerms N ℓ ℓ (0 : Fin N)).Nonempty ↔ (0 < ℓ ∧ ℓ ≤ N) := by
  constructor
  · rintro ⟨f, hf⟩
    have hf' : Valid ℓ ℓ (0 : Fin N) f := by
      simpa [validPerms] using hf
    exact ⟨pos_of_valid hf', le_of_valid hf'⟩
  · rintro ⟨hℓ, hlN⟩
    obtain ⟨f, hf⟩ := exists_valid hℓ hlN
    exact ⟨f, by simpa [validPerms] using hf⟩

/-! ## 具体点での突き合わせ（`decide`、`native_decide` 不使用）

上の一般定理と、置換を核で全数評価した結果が一致することを具体点で
確かめる。定理が `validPerms` の**定義と噛み合っている**ことの回帰試験
であって、定理の証明ではない。独立の全数オラクルは
`research/nonvacuous_check.py`（N=1..7, ℓ=0..9 の 70 セルで一致）。 -/

section Concrete

/-- 領域内 (`0 < ℓ ≤ N`): 全数評価でも約束は非空。 -/
example : (validPerms 3 2 2 (0 : Fin 3)).Nonempty := by decide

/-- 同じことを一般定理から。両者が一致する。 -/
example : (validPerms 3 2 2 (0 : Fin 3)).Nonempty :=
  validPerms_nonempty_iff.mpr ⟨by omega, by omega⟩

/-- **空虚な領域** (`ℓ > N`): 全数評価でも約束は空。ここでは
`WinsAt` が反例なしで成立するため `gameValue_eq` は内容を持たない。 -/
example : ¬ (validPerms 3 4 4 (0 : Fin 3)).Nonempty := by decide

/-- 同じことを一般定理から。 -/
example : ¬ (validPerms 3 4 4 (0 : Fin 3)).Nonempty :=
  fun h => absurd (le_of_valid (by simpa [validPerms] using h.choose_spec)) (by omega)

/-- `ℓ = 0` も空（軌道は必ず `0` 自身を含む）。 -/
example : ¬ (validPerms 3 0 0 (0 : Fin 3)).Nonempty := by decide

end Concrete

/-! ## 定理9.6：どこに実質があるか

上の非空性の特徴づけと `TwoPointUpper.lean` の `gameValue_eq`（値の公式
`gameValue N ℓ = min (ℓ − 2) (k₁*(N, ℓ))`）を突き合わせ、定理9.6 が
実際に内容を持つ範囲を確定する。

* `N < ℓ`（空虚域）: 閉形式そのものが `k1Star_eq_zero_of_le` により
  `0` に崩壊する。これとは**独立の理由**で、約束を満たす `f` が
  存在しないため深さ `0` の木が空虚に勝つ（`gameValue_eq_zero_of_lt`）。
  二つの理由が同じ値 `0` に落ちること自体は、この節では主張しない
  （閉形式の崩壊は `N ≤ ℓ` 一般、`gameValue_eq_zero_of_lt` は
  `N < ℓ` の厳密な場合のみを扱う）。
* `0 < ℓ ≤ N`（非空虚域）: 値の公式が成り立ち、かつそれが定量化して
  いる約束 `validPerms N ℓ ℓ 0` 自体が非空である
  （`gameValue_eq_nonvacuous`）。これが定理9.6 の「実質を持つ」形。 -/

section HasContent

open PeriodicTM.QueryGame

/-- **閉形式の崩壊**: `N ≤ ℓ` のとき `k₁*(N, ℓ) = 0`。自然数減算で
`N - ℓ = 0` となり、`1` 以上のどの `m` についても `Kills N ℓ 0` が
（空虚にではなく）文字通り成り立つため。 -/
theorem k1Star_eq_zero_of_le {N ℓ : ℕ} (h : N ≤ ℓ) :
    PeriodicTM.TwoPointCore.k1Star N ℓ = 0 := by
  have hkills : PeriodicTM.TwoPointCore.Kills N ℓ 0 := by
    intro m _ hm1 _
    omega
  rw [PeriodicTM.TwoPointCore.k1Star]
  exact (Nat.find_eq_zero _).mpr hkills

/-- **空虚域でのゲーム値**: `N < ℓ` のとき `gameValue N ℓ = 0`。
理由は閉形式の崩壊とは独立: 約束 `Valid ℓ ℓ 0 f` を満たす `f` が
そもそも存在しない（`le_of_valid` に矛盾）ので、深さ `0` の木
（葉はダミー）が空虚に `WinsAt` を満たす。 -/
theorem gameValue_eq_zero_of_lt {N ℓ : ℕ} [NeZero N] (h : N < ℓ) :
    PeriodicTM.Upper.gameValue N ℓ = 0 := by
  have hmem : (0 : ℕ) ∈
      {q : ℕ | ∃ t : Tree N q, WinsAt ℓ ℓ (0 : Fin N) 1 t} := by
    refine ⟨Tree.leaf 0 0, ?_⟩
    intro f hf
    exact absurd (le_of_valid hf) (by omega)
  exact le_antisymm (Nat.sInf_le hmem) (Nat.zero_le _)

/-- **定理9.6・非空虚形**: `0 < ℓ ≤ N` では、値の公式
`gameValue N ℓ = min (ℓ − 2) (k₁*(N, ℓ))` が成り立つのに加え、それが
定量化している約束 `validPerms N ℓ ℓ 0` 自体が非空。すなわち定理9.6
はこの範囲で反例なしの空虚な真理ではなく、実際の証拠つきの主張になる。 -/
theorem gameValue_eq_nonvacuous {N ℓ : ℕ} [NeZero N] (hN : 2 ≤ N) (hℓ : 2 ≤ ℓ)
    (hlN : ℓ ≤ N) :
    (validPerms N ℓ ℓ (0 : Fin N)).Nonempty ∧
      PeriodicTM.Upper.gameValue N ℓ = min (ℓ - 2) (PeriodicTM.TwoPointCore.k1Star N ℓ) :=
  ⟨validPerms_nonempty_iff.mpr ⟨by omega, hlN⟩, PeriodicTM.Upper.gameValue_eq hN hℓ⟩

end HasContent

#print axioms exists_valid
#print axioms le_of_valid
#print axioms validPerms_nonempty_iff
#print axioms gameValue_eq_nonvacuous
#print axioms gameValue_eq_zero_of_lt

end PeriodicTM.Nonvacuous
