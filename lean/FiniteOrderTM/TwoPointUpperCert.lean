/-
FiniteOrderTM/TwoPointUpperCert.lean
— 上界の構成に対する**変異注入**（葉の出力が本当に効いているか）

`TwoPointUpper.lean` の記号証明は「勝てる」としか言わない。証明が
`Runs` / `WinsAt` の空虚さに寄りかかっていないことは、**わざと壊した木が
負けること**を独立に評価して確かめる（`research/…` の検査と同じ作法:
検出力と誤検出を対で測る）。

* `pin_wins_N6_l4` — 構成した木は勝つ（記号証明 `exists_pin_tree` から）。
* `badPin_loses` — ピン留めの葉 `(f^(ℓ−2) 0, 1)` を `(1, f^(ℓ−2) 0)` に
  入れ替えると負ける。
* `badKill_loses` — 殺しの葉 `(1,0)` と `(0,1)` を取り違えると負ける。

後ろ 2 つは Layer-2（`native_decide` による有界評価）。評価される定義は
`QueryGame.lean` の記号的なもの。N = 6・ℓ = 4（`validPerms` は Fin 6 の
置換 720 個の部分集合）なので、`lake build` に入れても安い。
-/
import FiniteOrderTM.TwoPointUpper

namespace PeriodicTM.Upper

open PeriodicTM.QueryGame

/-- 構成した木は勝つ（`TwoPointUpper.lean` の記号証明の具体化）。
`QueryGame.exists_depth2_N6_n4_l4`（`native_decide` で「深さ 2 の勝ち筋が
存在する」）と独立に一致する。 -/
theorem pin_wins_N6_l4 : ∃ t : Tree 6 2, WinsAt 4 4 (0 : Fin 6) 1 t :=
  exists_pin_tree (N := 6) (ℓ := 4) (by norm_num) (by norm_num)

/-- 変異: ピン留めの葉の出力を左右入れ替えた木。 -/
def badPin : (q : ℕ) → Fin 6 → Bool → Tree 6 q
  | 0, cur, seen => if seen then .leaf 1 0 else .leaf 1 cur
  | _ + 1, cur, seen => .node cur fun y => badPin _ y (seen || decide (y = 1))

/-- **変異注入（native_decide）**: 入れ替えた木は負ける。
すなわち `walkZero` の葉 `(f^(ℓ−2) 0, 1)` は本質的で、
勝利の証明は `WinsAt` の空虚さから来ていない。 -/
theorem badPin_loses : ¬ WinsAt 4 4 (0 : Fin 6) 1 (badPin 2 0 false) := by
  rw [winsAt_iff_forall_mem]
  native_decide

/-- 変異: 殺しの葉の 2 つの出力を取り違えた木。 -/
def badKill : (q : ℕ) → Fin 6 → Bool → Bool → Tree 6 q
  | 0, _, hit0, closed => if closed && !hit0 then .leaf 1 0 else .leaf 0 1
  | _ + 1, cur, hit0, closed =>
      .node cur fun y =>
        badKill _ y (hit0 || decide (y = 0)) (closed || decide (y = 1))

/-- **変異注入（native_decide）**: 取り違えた木は負ける。
すなわち `walkOne` の「閉じたが 0 に触れていないときだけ `(0,1)`」という
場合分けは本質的。 -/
theorem badKill_loses : ¬ WinsAt 4 4 (0 : Fin 6) 1 (badKill 2 1 false false) := by
  rw [winsAt_iff_forall_mem]
  native_decide

end PeriodicTM.Upper

#print axioms PeriodicTM.Upper.pin_wins_N6_l4
#print axioms PeriodicTM.Upper.badPin_loses
#print axioms PeriodicTM.Upper.badKill_loses
