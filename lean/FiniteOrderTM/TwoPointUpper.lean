/-
FiniteOrderTM/TwoPointUpper.lean
— 定理9.6 の上界: 深さ `min (ℓ−2, k₁*(N, ℓ))` の勝利木の構成

research/09 の「上界（2 つの勝ち筋）」の機械化。

* **d ピン留めルート**（深さ `ℓ − 2`）: `0` から前方に `ℓ−2` 歩あるく。
  途中で `1` を見たら同一軌道が確定するので型3恒真対 `(1, 0)`。
  見なければ `1` は `{f^0 0, …, f^(ℓ−2) 0}` の外なので、別軌道か
  さもなくば `1 = f^(ℓ−1) 0` に**ピン留め**される。どちらでも出力
  `(f^(ℓ−2) 0, 1)` が良い（前者は `goodOutput_cross`、後者は
  `goodOutput_pin`）。紙の「型2出力」を、位置指定つき反射で書いたもの。
* **別軌道殺しルート**（深さ `k₁*`）: `1` から `k₁*` 歩あるく。
  `0` に届けば同一軌道、届かずに閉じたら別軌道が確定、どちらでもなければ
  `1` の軌道は `k₁*+1` 点以上あり、`Kills` が別軌道を禁じるので同一軌道。

下界（`TwoPointLowerBound.lean` の `two_point_lower_bound`）と合わせて
`two_point_value` が定理9.6 そのもの。`native_decide` 不使用・sorry 0。
-/
import FiniteOrderTM.TwoPointReflect
import FiniteOrderTM.TwoPointClaimAGeneral
-- 最後の `two_point_value`（上界＋下界＝定理9.6）のためだけに使う。
import FiniteOrderTM.TwoPointLowerBound

namespace PeriodicTM.Upper

open Equiv Finset
open PeriodicTM.QueryGame (Tree GoodOutput IsReflection Runs Valid WinsAt)

variable {N : ℕ}

/-! ### 共通の小道具 -/

section Aux

/-- `x` が `f^j` の不動点なら、冪の作用は指数の法 `j` に落ちる。 -/
theorem pow_apply_mod {f : Perm (Fin N)} {x : Fin N} {j : ℕ} (hj : 0 < j)
    (hx : (f ^ j) x = x) : ∀ i : ℕ, (f ^ (i % j)) x = (f ^ i) x := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    by_cases hij : i < j
    · rw [Nat.mod_eq_of_lt hij]
    · have hji : j ≤ i := by omega
      have hsplit : (f ^ (i - j)) x = (f ^ i) x := by
        conv_rhs => rw [← Nat.sub_add_cancel hji]
        rw [pow_add]
        simp [Perm.mul_apply, hx]
      rw [Nat.mod_eq_sub_mod hji, ih (i - j) (by omega), hsplit]

/-- `f^j` が `x` を固定するなら、`x` の軌道は `{f^i x : i < j}` に収まる。 -/
theorem exists_pow_lt_of_period {f : Perm (Fin N)} {x y : Fin N} {j : ℕ}
    (hj : 0 < j) (hx : (f ^ j) x = x) (h : f.SameCycle x y) :
    ∃ i < j, (f ^ i) x = y := by
  obtain ⟨i, -, hi⟩ := h.exists_pow_eq'
  exact ⟨i % j, Nat.mod_lt _ hj, by rw [pow_apply_mod hj hx, hi]⟩

/-- 冪の作用は同一軌道を与える。 -/
theorem sameCycle_pow (f : Perm (Fin N)) (x : Fin N) (i : ℕ) :
    f.SameCycle x ((f ^ i) x) :=
  ⟨(i : ℤ), by rw [zpow_natCast]⟩

/-- 反射は `f` を `f⁻¹` に共役する（点ごとの形 `ι ∘ f = f⁻¹ ∘ ι`）。 -/
theorem reflection_apply_f {f : Perm (Fin N)} {ι : Fin N → Fin N}
    (h : IsReflection f ι) (y : Fin N) : ι (f y) = f⁻¹ (ι y) := by
  have hc := h.conj_eq_inv (ι y)
  rwa [h.1 y] at hc

/-- `2 ≤ N` なら `Fin N` の `0` と `1` は異なる。 -/
theorem zero_ne_one_fin [NeZero N] (hN : 2 ≤ N) : (0 : Fin N) ≠ 1 := by
  intro hc
  have h := congrArg Fin.val hc
  simp [Nat.mod_eq_of_lt (by omega : 1 < N)] at h

end Aux

/-! ### d ピン留めルート（深さ `ℓ − 2`） -/

section Pin

variable [NeZero N]

/-- **ピン留めの葉**: `f^ℓ = 1` かつ `1 = f^(ℓ−1) 0` なら、
出力 `(f^(ℓ−2) 0, 1)` は良い。

紙の「型2出力（`2d ≡ γ−δ`）」に当たる。反射 `ρ` を `ρ 1 = 1` に
合わせると、`f 1 = 0` から `ρ 0 = f⁻¹ (ρ 1) = f⁻¹ 1 = f^(ℓ−2) 0`
が自動的に出る。 -/
theorem goodOutput_pin {f : Perm (Fin N)} {ℓ : ℕ} (hℓ : 2 ≤ ℓ)
    (hpow : f ^ ℓ = 1) (h1 : (f ^ (ℓ - 1)) 0 = 1) :
    GoodOutput (0 : Fin N) 1 f ((f ^ (ℓ - 2)) 0) 1 := by
  have hR0 := PeriodicTM.Reflect.refl0_isReflection f
  set ι := PeriodicTM.Reflect.refl0 f with hιdef
  -- `ρ 1 = 1` になるようにシフト量 `k` をとる
  obtain ⟨k, -, hk⟩ := (hR0.2.1 1).symm.exists_pow_eq'
  have hρ : IsReflection f (fun z => (f ^ k) (ι z)) :=
    PeriodicTM.Reflect.isReflection_pow_comp hR0 k
  -- `f 1 = 0`
  have hf1 : f 1 = 0 := by
    have hsplit : (f ^ ℓ) 0 = f ((f ^ (ℓ - 1)) 0) := by
      conv_lhs => rw [show ℓ = 1 + (ℓ - 1) from by omega]
      rw [pow_add, pow_one]
      rfl
    rw [h1] at hsplit
    rw [← hsplit, hpow]
    rfl
  -- `f⁻¹ 1 = f^(ℓ−2) 0`
  have hinv1 : f⁻¹ 1 = (f ^ (ℓ - 2)) 0 := by
    have hsplit : (f ^ (ℓ - 1)) 0 = f ((f ^ (ℓ - 2)) 0) := by
      conv_lhs => rw [show ℓ - 1 = 1 + (ℓ - 2) from by omega]
      rw [pow_add, pow_one]
      rfl
    rw [hsplit] at h1
    rw [← h1]
    simp
  refine ⟨fun z => (f ^ k) (ι z), hρ, ?_, hk⟩
  show (f ^ k) (ι 0) = (f ^ (ℓ - 2)) 0
  have hstep := reflection_apply_f hρ 1
  simp only [hf1] at hstep
  -- hstep : (f ^ k) (ι 0) = f⁻¹ ((f ^ k) (ι 1))
  rw [hstep, hk, hinv1]

/-- `0` から前方に歩く決定木。`cur` は現在地、`seen` は「答えに `1` が
出たか」。葉では `seen` なら型3恒真対 `(1, 0)`、そうでなければ
`(cur, 1)`（＝ピン留め出力）。 -/
def walkZero : (q : ℕ) → Fin N → Bool → Tree N q
  | 0, cur, seen => if seen then .leaf 1 0 else .leaf cur 1
  | _ + 1, cur, seen => .node cur fun y => walkZero _ y (seen || decide (y = 1))

/-- 歩行木の不変量つき正当性。`i` はこれまでに歩いた歩数。 -/
theorem walkZero_runs {ℓ : ℕ} (hℓ : 2 ≤ ℓ) {f : Perm (Fin N)}
    (hpow : f ^ ℓ = 1) :
    ∀ (q i : ℕ) (seen : Bool), i + q = ℓ - 2 →
      (seen = true → f.SameCycle 0 1) →
      (seen = false → ∀ j ≤ i, (f ^ j) 0 ≠ 1) →
      Runs (0 : Fin N) 1 (walkZero q ((f ^ i) 0) seen) f := by
  intro q
  induction q with
  | zero =>
    intro i seen hi htrue hfalse
    have hi' : i = ℓ - 2 := by omega
    subst hi'
    cases seen with
    | true =>
      show Runs (0 : Fin N) 1 (Tree.leaf 1 0) f
      exact PeriodicTM.Reflect.goodOutput_one_zero (htrue rfl)
    | false =>
      show Runs (0 : Fin N) 1 (Tree.leaf ((f ^ (ℓ - 2)) 0) 1) f
      show GoodOutput (0 : Fin N) 1 f ((f ^ (ℓ - 2)) 0) 1
      by_cases hsc : f.SameCycle 0 1
      · -- 同一軌道: `1` は `f^(ℓ−1) 0` にピン留めされる
        have hfix : (f ^ ℓ) (0 : Fin N) = 0 := by rw [hpow]; rfl
        obtain ⟨j, hjlt, hj⟩ :=
          exists_pow_lt_of_period (by omega : 0 < ℓ) hfix hsc
        have hjge : ℓ - 2 < j := by
          by_contra hcon
          exact hfalse rfl j (by omega) hj
        have hjeq : j = ℓ - 1 := by omega
        subst hjeq
        exact goodOutput_pin hℓ hpow hj
      · exact PeriodicTM.Reflect.goodOutput_cross hsc
          (sameCycle_pow f 0 (ℓ - 2)) (Perm.SameCycle.refl f 1)
  | succ q ih =>
    intro i seen hi htrue hfalse
    show Runs (0 : Fin N) 1
      (walkZero q (f ((f ^ i) 0))
        (seen || decide (f ((f ^ i) 0) = 1))) f
    have hnext : f ((f ^ i) 0) = (f ^ (i + 1)) 0 := by
      rw [pow_succ']
      rfl
    rw [hnext]
    refine ih (i + 1) (seen || decide ((f ^ (i + 1)) (0 : Fin N) = 1))
      (by omega) ?_ ?_
    · intro hor
      rcases Bool.or_eq_true_iff.mp hor with hs | hy
      · exact htrue hs
      · have hy1 : (f ^ (i + 1)) (0 : Fin N) = 1 := of_decide_eq_true hy
        exact hy1 ▸ sameCycle_pow f 0 (i + 1)
    · intro hor j hj
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hor
      obtain ⟨hs, hy⟩ := hor
      rcases Nat.lt_or_ge j (i + 1) with hlt | hge
      · exact hfalse hs j (by omega)
      · have hji : j = i + 1 := by omega
        subst hji
        exact hy

/-- `0` から `ℓ − 2` 歩あるく木は勝つ。 -/
theorem walkZero_wins {ℓ : ℕ} (hN : 2 ≤ N) (hℓ : 2 ≤ ℓ) :
    WinsAt ℓ ℓ (0 : Fin N) 1 (walkZero (ℓ - 2) 0 false) := by
  intro f hf
  have h := walkZero_runs hℓ hf.1 (ℓ - 2) 0 false (by omega)
    (by simp) (by
      intro _ j hj
      have hj0 : j = 0 := by omega
      subst hj0
      simpa using (zero_ne_one_fin hN))
  simpa using h

/-- **上界その1（ピン留め）**: 深さ `ℓ − 2` の勝利木が存在する。 -/
theorem exists_pin_tree {ℓ : ℕ} (hN : 2 ≤ N) (hℓ : 2 ≤ ℓ) :
    ∃ t : Tree N (ℓ - 2), WinsAt ℓ ℓ (0 : Fin N) 1 t :=
  ⟨_, walkZero_wins hN hℓ⟩

end Pin

/-! ### 別軌道殺しルート（深さ `k₁*`） -/

section Kill

variable [NeZero N]

/-- 軌道が `k` 歩以内に閉じ、その間 `0` に触れなければ、`0` と `1` は
別軌道（閉じた軌道は歩いた点で尽きるので `0` は入りようがない）。 -/
theorem not_sameCycle_of_closed {f : Perm (Fin N)} {k j : ℕ}
    (hj1 : 1 ≤ j) (hjk : j ≤ k) (hclose : (f ^ j) (1 : Fin N) = 1)
    (hno0 : ∀ r ≤ k, (f ^ r) (1 : Fin N) ≠ 0) :
    ¬ f.SameCycle 0 1 := by
  intro hsc
  obtain ⟨r, hrlt, hr⟩ :=
    exists_pow_lt_of_period (by omega : 0 < j) hclose hsc.symm
  exact hno0 r (by omega) hr

/-- **殺しの葉（点数勘定）**: `Kills N ℓ k` の下で、`1` から `k` 歩
歩いても軌道が閉じないなら、`0` と `1` は同一軌道でしかありえない。

別軌道だとすると `1` の軌道長 `m` は (a) `ℓ` の約数、(b) `0` の軌道と
交わらないので `m ≤ N − ℓ`、(c) 歩いた `k+1` 点が相異なるので
`m ≥ k+1`。`Kills` はこの窓に約数が無いことを言っている。 -/
theorem sameCycle_of_not_closed {ℓ k : ℕ} {f : Perm (Fin N)}
    (hℓ : 0 < ℓ) (hkill : PeriodicTM.TwoPointCore.Kills N ℓ k)
    (hf : Valid ℓ ℓ (0 : Fin N) f)
    (hopen : ∀ r, 1 ≤ r → r ≤ k → (f ^ r) (1 : Fin N) ≠ 1) :
    f.SameCycle 0 1 := by
  by_contra hd
  set m := #{y | f.SameCycle (1 : Fin N) y} with hm
  have hdvd : m ∣ ℓ := PeriodicTM.ClaimA.orbit_card_dvd f hf.1 1
  have hmle : m ≤ ℓ := Nat.le_of_dvd hℓ hdvd
  -- (b) 軌道が交わらないので `ℓ + m ≤ N`
  have hdisj := PeriodicTM.ClaimA.orbit_disjoint f hd
  have hunion : #(({y | f.SameCycle (0 : Fin N) y} : Finset (Fin N)) ∪
      ({y | f.SameCycle (1 : Fin N) y} : Finset (Fin N))) = ℓ + m := by
    rw [Finset.card_union_of_disjoint hdisj, hf.2]
  have hle : #(({y | f.SameCycle (0 : Fin N) y} : Finset (Fin N)) ∪
      ({y | f.SameCycle (1 : Fin N) y} : Finset (Fin N))) ≤ N := by
    calc #(({y | f.SameCycle (0 : Fin N) y} : Finset (Fin N)) ∪
          ({y | f.SameCycle (1 : Fin N) y} : Finset (Fin N)))
        ≤ #(Finset.univ : Finset (Fin N)) := Finset.card_le_univ _
      _ = N := by simp
  -- (c) 歩いた `k+1` 点は相異なる
  have key : ∀ a b : ℕ, a ≤ b → b ≤ k →
      (f ^ a) (1 : Fin N) = (f ^ b) 1 → a = b := by
    intro a b hab hbk heq
    by_contra hne
    have hsplit : (f ^ b) (1 : Fin N) = (f ^ a) ((f ^ (b - a)) 1) := by
      conv_lhs => rw [← Nat.add_sub_cancel' hab]
      rw [pow_add]
      rfl
    rw [hsplit] at heq
    exact hopen (b - a) (by omega) (by omega) ((f ^ a).injective heq).symm
  have hcard : k + 1 ≤ m := by
    have hmaps : ∀ a ∈ Finset.range (k + 1), (f ^ a) (1 : Fin N) ∈
        ({y | f.SameCycle (1 : Fin N) y} : Finset (Fin N)) := by
      intro a _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact sameCycle_pow f 1 a
    have hinj : Set.InjOn (fun a => (f ^ a) (1 : Fin N))
        (Finset.range (k + 1)) := by
      intro a ha b hb hab
      simp only [Finset.coe_range, Set.mem_Iio] at ha hb
      rcases le_total a b with h | h
      · exact key a b h (by omega) hab
      · exact (key b a h (by omega) hab.symm).symm
    calc k + 1 = #(Finset.range (k + 1)) := by simp
      _ ≤ m := Finset.card_le_card_of_injOn _ hmaps hinj
  have := hkill m hmle hcard hdvd
  omega

/-- `1` から前方に歩く決定木。`hit0` は「答えに `0` が出たか」、
`closed` は「答えに `1` が出たか（＝軌道が閉じたか）」。
葉では「閉じたが `0` に触れていない」ときだけ別軌道確定で `(0, 1)`、
それ以外は同一軌道が確定するので型3恒真対 `(1, 0)`。 -/
def walkOne : (q : ℕ) → Fin N → Bool → Bool → Tree N q
  | 0, _, hit0, closed => if closed && !hit0 then .leaf 0 1 else .leaf 1 0
  | _ + 1, cur, hit0, closed =>
      .node cur fun y =>
        walkOne _ y (hit0 || decide (y = 0)) (closed || decide (y = 1))

/-- 歩行木の不変量つき正当性。`i` はこれまでに歩いた歩数。 -/
theorem walkOne_runs {ℓ k : ℕ} (hℓ : 0 < ℓ)
    (hkill : PeriodicTM.TwoPointCore.Kills N ℓ k) {f : Perm (Fin N)}
    (hf : Valid ℓ ℓ (0 : Fin N) f) :
    ∀ (q i : ℕ) (hit0 closed : Bool), i + q = k →
      (hit0 = true → f.SameCycle 0 1) →
      (closed = true → ∃ j, 1 ≤ j ∧ j ≤ i ∧ (f ^ j) (1 : Fin N) = 1) →
      (hit0 = false → ∀ r ≤ i, (f ^ r) (1 : Fin N) ≠ 0) →
      (closed = false → ∀ r, 1 ≤ r → r ≤ i → (f ^ r) (1 : Fin N) ≠ 1) →
      Runs (0 : Fin N) 1 (walkOne q ((f ^ i) 1) hit0 closed) f := by
  intro q
  induction q with
  | zero =>
    intro i hit0 closed hi htrue hclosed hno0 hopen
    have hi' : i = k := by omega
    subst hi'
    have hgood10 : f.SameCycle 0 1 →
        Runs (0 : Fin N) 1 (Tree.leaf (1 : Fin N) 0) f := fun h =>
      PeriodicTM.Reflect.goodOutput_one_zero h
    cases hit0 with
    | true =>
      cases closed with
      | true => exact hgood10 (htrue rfl)
      | false => exact hgood10 (htrue rfl)
    | false =>
      cases closed with
      | true =>
        obtain ⟨j, hj1, hjk, hj⟩ := hclosed rfl
        have hd := not_sameCycle_of_closed hj1 hjk hj (hno0 rfl)
        show Runs (0 : Fin N) 1 (Tree.leaf (0 : Fin N) 1) f
        exact PeriodicTM.Reflect.goodOutput_cross hd
          (Perm.SameCycle.refl f 0) (Perm.SameCycle.refl f 1)
      | false =>
        exact hgood10 (sameCycle_of_not_closed hℓ hkill hf (hopen rfl))
  | succ q ih =>
    intro i hit0 closed hi htrue hclosed hno0 hopen
    show Runs (0 : Fin N) 1
      (walkOne q (f ((f ^ i) 1))
        (hit0 || decide (f ((f ^ i) 1) = 0))
        (closed || decide (f ((f ^ i) 1) = 1))) f
    have hnext : f ((f ^ i) (1 : Fin N)) = (f ^ (i + 1)) 1 := by
      rw [pow_succ']
      rfl
    rw [hnext]
    refine ih (i + 1) (hit0 || decide ((f ^ (i + 1)) (1 : Fin N) = 0))
      (closed || decide ((f ^ (i + 1)) (1 : Fin N) = 1)) (by omega) ?_ ?_ ?_ ?_
    · -- hit0 が立った → 0 と 1 は同一軌道
      intro hor
      rcases Bool.or_eq_true_iff.mp hor with hs | hy
      · exact htrue hs
      · have hy0 : (f ^ (i + 1)) (1 : Fin N) = 0 := of_decide_eq_true hy
        exact ((hy0 ▸ sameCycle_pow f 1 (i + 1)) : f.SameCycle 1 0).symm
    · -- closed が立った → 閉じる歩数の証拠
      intro hor
      rcases Bool.or_eq_true_iff.mp hor with hs | hy
      · obtain ⟨j, hj1, hjk, hj⟩ := hclosed hs
        exact ⟨j, hj1, by omega, hj⟩
      · exact ⟨i + 1, by omega, le_refl _, of_decide_eq_true hy⟩
    · -- hit0 が立たない → i+1 歩まで 0 に触れていない
      intro hor r hr
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hor
      obtain ⟨hs, hy⟩ := hor
      rcases Nat.lt_or_ge r (i + 1) with hlt | hge
      · exact hno0 hs r (by omega)
      · have hri : r = i + 1 := by omega
        subst hri
        exact hy
    · -- closed が立たない → i+1 歩まで閉じていない
      intro hor r hr1 hr
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hor
      obtain ⟨hs, hy⟩ := hor
      rcases Nat.lt_or_ge r (i + 1) with hlt | hge
      · exact hopen hs r hr1 (by omega)
      · have hri : r = i + 1 := by omega
        subst hri
        exact hy

/-- `1` から `k` 歩あるく木は、`Kills N ℓ k` の下で勝つ。 -/
theorem walkOne_wins {ℓ k : ℕ} (hN : 2 ≤ N) (hℓ : 0 < ℓ)
    (hkill : PeriodicTM.TwoPointCore.Kills N ℓ k) :
    WinsAt ℓ ℓ (0 : Fin N) 1 (walkOne k 1 false false) := by
  intro f hf
  have h := walkOne_runs hℓ hkill hf k 0 false false (by omega)
    (by simp) (by simp)
    (by
      intro _ r hr
      have hr0 : r = 0 := by omega
      subst hr0
      simpa using (zero_ne_one_fin hN).symm)
    (by
      intro _ r hr1 hr
      omega)
  simpa using h

/-- **上界その2（別軌道殺し）**: 深さ `k₁*(N, ℓ)` の勝利木が存在する。 -/
theorem exists_kill_tree {ℓ : ℕ} (hN : 2 ≤ N) (hℓ : 0 < ℓ) :
    ∃ t : Tree N (PeriodicTM.TwoPointCore.k1Star N ℓ),
      WinsAt ℓ ℓ (0 : Fin N) 1 t :=
  ⟨_, walkOne_wins hN hℓ (PeriodicTM.TwoPointCore.k1Star_kills N ℓ)⟩

end Kill

/-! ### 定理 9.6 -/

section Main

variable [NeZero N]

/-- **定理9.6（上界）**: 深さ `min (ℓ − 2, k₁*(N, ℓ))` の勝利木が存在する。 -/
theorem two_point_upper_bound {ℓ : ℕ} (hN : 2 ≤ N) (hℓ : 2 ≤ ℓ) :
    ∃ t : Tree N (min (ℓ - 2) (PeriodicTM.TwoPointCore.k1Star N ℓ)),
      WinsAt ℓ ℓ (0 : Fin N) 1 t := by
  rcases le_total (ℓ - 2) (PeriodicTM.TwoPointCore.k1Star N ℓ) with h | h
  · rw [min_eq_left h]
    exact exists_pin_tree hN hℓ
  · rw [min_eq_right h]
    exact exists_kill_tree hN (by omega)

/-- **定理 9.6（値の公式）**: 2 点整合ゲームの値はちょうど
`min (ℓ − 2, k₁*(N, ℓ))`。すなわち、それ未満の深さのどの適応的決定木も
勝てず（下界）、その深さの勝利木は存在する（上界）。 -/
theorem two_point_value {ℓ : ℕ} (hN : 2 ≤ N) (hℓ : 3 ≤ ℓ) :
    (∀ q < min (ℓ - 2) (PeriodicTM.TwoPointCore.k1Star N ℓ),
        ¬ ∃ t : Tree N q, WinsAt ℓ ℓ (0 : Fin N) 1 t) ∧
      (∃ t : Tree N (min (ℓ - 2) (PeriodicTM.TwoPointCore.k1Star N ℓ)),
        WinsAt ℓ ℓ (0 : Fin N) 1 t) :=
  ⟨fun _ hq => PeriodicTM.ClaimA.two_point_lower_bound hℓ hq,
    two_point_upper_bound hN (by omega)⟩

/-- 2 点整合ゲームの**値**: 勝利する適応的決定木が存在する最小の深さ。
（`Nat.sInf` なので、勝てる深さが無いときは `0` になる。実際には上界が
常に存在するので `gameValue_eq` の下でその角は起きない。） -/
noncomputable def gameValue (N ℓ : ℕ) [NeZero N] : ℕ :=
  sInf {q : ℕ | ∃ t : Tree N q, WinsAt ℓ ℓ (0 : Fin N) 1 t}

/-- **定理 9.6**: `value(N, ℓ) = min(ℓ − 2, k₁*(N, ℓ))`。
上界（最小性の上からの評価）と下界（それ未満では勝てない）の合成。 -/
theorem gameValue_eq {ℓ : ℕ} (hN : 2 ≤ N) (hℓ : 3 ≤ ℓ) :
    gameValue N ℓ = min (ℓ - 2) (PeriodicTM.TwoPointCore.k1Star N ℓ) := by
  have hmem : min (ℓ - 2) (PeriodicTM.TwoPointCore.k1Star N ℓ) ∈
      {q : ℕ | ∃ t : Tree N q, WinsAt ℓ ℓ (0 : Fin N) 1 t} :=
    two_point_upper_bound hN (by omega)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra hcon
  exact PeriodicTM.ClaimA.two_point_lower_bound hℓ (not_le.mp hcon)
    (Nat.sInf_mem ⟨_, hmem⟩)

end Main

/-! ### 測定表との突き合わせ

`research/data/query_game_values.csv`（`research/gen_value_table.py` が
厳密ソルバで生成）の `solver_value` 欄と、閉形式
`min (ℓ − 2, k₁*(N, ℓ))` が一致することを検査する。**`k₁*` の Lean 定義
（`Kills` の最小点）が測定と噛み合っていること**の回帰試験であって、
定理そのものの証明ではない。`native_decide` は使わない。 -/

section Table

open PeriodicTM.TwoPointCore

/-- `Nat.find` は核で簡約されないので、`min (ℓ−2) (k₁*(N,ℓ)) = v` を
`decide` にかけられる形に言い換える。 -/
def CellOK (N ℓ v : ℕ) : Prop :=
  v ≤ ℓ - 2 ∧ (∀ k < v, ¬ Kills N ℓ k) ∧ (v = ℓ - 2 ∨ Kills N ℓ v)

instance : Decidable (CellOK N ℓ v) := by unfold CellOK; infer_instance

theorem min_k1Star_eq_of_cellOK {N ℓ v : ℕ} (h : CellOK N ℓ v) :
    min (ℓ - 2) (k1Star N ℓ) = v := by
  obtain ⟨hv, hlow, hhi⟩ := h
  have hge : v ≤ k1Star N ℓ := by
    rw [k1Star, Nat.le_find_iff]
    exact hlow
  rcases hhi with hveq | hk
  · omega
  · have hle : k1Star N ℓ ≤ v := Nat.find_le hk
    omega

/-- 厳密ソルバで**測定済み**の 42 セル `(N, ℓ, 測定値)`。
`predicted-only` の 3 セル（N=12, ℓ=4,5,6）は測定されていないので入れない。 -/
def measuredCells : List (ℕ × ℕ × ℕ) :=
  [(2,2,0),(3,2,0),(4,2,0),(5,2,0),(6,2,0),(7,2,0),(8,2,0),(9,2,0),
   (10,2,0),(11,2,0),(12,2,0),
   (3,3,0),(4,3,1),(5,3,1),(6,3,1),(7,3,1),(8,3,1),(9,3,1),(10,3,1),
   (11,3,1),(12,3,1),
   (4,4,0),(5,4,1),(6,4,2),(7,4,2),(8,4,2),(9,4,2),(10,4,2),(11,4,2),
   (5,5,0),(6,5,1),(7,5,1),(8,5,1),(9,5,1),(10,5,3),(11,5,3),
   (6,6,0),(7,6,1),(8,6,2),(9,6,3),(10,6,3),(11,6,3)]

theorem measuredCells_ok : ∀ c ∈ measuredCells, CellOK c.1 c.2.1 c.2.2 := by
  decide

/-- **閉形式は測定値に一致する**（42 セル）。 -/
theorem closed_form_matches_measured :
    ∀ c ∈ measuredCells, min (c.2.1 - 2) (k1Star c.1 c.2.1) = c.2.2 :=
  fun c hc => min_k1Star_eq_of_cellOK (measuredCells_ok c hc)

/-- 測定表と `QueryGame.lean` の `native_decide` 証明書の噛み合わせ:
N=5, ℓ=3 では値 1、N=6, ℓ=4 と N=7, ℓ=4 では値 2。 -/
example : min (3 - 2) (k1Star 5 3) = 1 := min_k1Star_eq_of_cellOK (by decide)
example : min (4 - 2) (k1Star 6 4) = 2 := min_k1Star_eq_of_cellOK (by decide)
example : min (4 - 2) (k1Star 7 4) = 2 := min_k1Star_eq_of_cellOK (by decide)

end Table

end PeriodicTM.Upper

#print axioms PeriodicTM.Upper.walkZero_wins
#print axioms PeriodicTM.Upper.walkOne_wins
#print axioms PeriodicTM.Upper.two_point_upper_bound
#print axioms PeriodicTM.Upper.two_point_value
#print axioms PeriodicTM.Upper.gameValue_eq
