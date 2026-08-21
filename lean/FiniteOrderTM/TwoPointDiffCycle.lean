/-
FiniteOrderTM/TwoPointDiffCycle.lean
— 別軌道完成の強化版: 未開示ラベルの配置内訳を露出する
  （research/18 の隙3・資源三択の「D」）

`completion_survives` は別軌道完成の存在（∃f）しか言わないが、
両成分未開示の出力対 (U, U) の撃墜には「未開示ラベルを 1 の軌道側に
置けるか、置けないなら全ての未開示ラベルが 1 の軌道の外」という
配置の情報が要る（research/18 の場合分け表）。ここでは
`formula_to_completion` と同じ構成をやり直し、その内訳を結論に足す。

**BUILD NOTE**: root（`FiniteOrderTM.lean`）非取込。検査は
`lake env lean FiniteOrderTM/TwoPointDiffCycle.lean`。
-/
import FiniteOrderTM.TwoPointClaimAGeneral

namespace PeriodicTM.ClaimA

open Equiv Finset

variable {N : ℕ}

/-! ### 右側サイクルの軌道補題（既存の左側版の鏡像） -/

section RightSide

variable {α : Type*} [DecidableEq α]

/-- `l₂` の点では積の反復は `l₂` 側の反復に一致する
（`mul_pow_apply_of_mem` の右側版）。 -/
theorem mul_pow_apply_of_mem_right {l₁ l₂ : List α}
    (hd : List.Disjoint l₁ l₂) :
    ∀ (k : ℕ) {x : α}, x ∈ l₂ →
      ((l₁.formPerm * l₂.formPerm) ^ k) x = (l₂.formPerm ^ k) x := by
  intro k
  induction k with
  | zero => intro x _; simp
  | succ k ih =>
    intro x hx
    rw [pow_succ, pow_succ, Perm.mul_apply, Perm.mul_apply, Perm.mul_apply]
    rw [List.formPerm_apply_of_notMem
      (fun h => hd h (List.formPerm_apply_mem_of_mem hx))]
    exact ih (List.formPerm_apply_mem_of_mem hx)

/-- `l₂` 上の 2 点は積の同一軌道（`formPerm_sameCycle` の右側版）。 -/
theorem sameCycle_right {l₁ l₂ : List α} (h₂ : l₂.Nodup)
    (hd : List.Disjoint l₁ l₂) {x y : α} (hx : x ∈ l₂) (hy : y ∈ l₂) :
    Perm.SameCycle (l₁.formPerm * l₂.formPerm) x y := by
  obtain ⟨k, hk⟩ := formPerm_exists_pow h₂ hx hy
  exact ⟨(k : ℤ), by
    rw [zpow_natCast, mul_pow_apply_of_mem_right hd k hx]
    exact hk⟩

/-- `l₂` の点から積で到達できる点は `l₂` の中だけ
（`sameCycle_mem_of_mem` の右側版）。 -/
theorem sameCycle_mem_of_mem_right [Finite α] {l₁ l₂ : List α}
    (hd : List.Disjoint l₁ l₂) {x y : α} (hx : x ∈ l₂)
    (h : Perm.SameCycle (l₁.formPerm * l₂.formPerm) x y) : y ∈ l₂ := by
  obtain ⟨i, _, rfl⟩ := h.exists_pow_eq'
  rw [mul_pow_apply_of_mem_right hd i hx]
  exact formPerm_pow_mem hx i

end RightSide

/-! ### 強化版の存在定理 -/

/-- 別軌道完成と、未開示ラベルの配置資源。`hres` の左は
「1 の軌道に乗る未開示ラベル `u`（0 の軌道の外）」、右は
「未開示ラベルはすべて 1 の軌道の外」。 -/
structure DiffCycleData (N ℓ : ℕ) [NeZero N] (s : AdvState) where
  f : Perm (Fin N)
  comp : IsCompletion N ℓ s f
  hdiff : ¬ f.SameCycle 0 1
  hres :
    (∃ u : ℕ, s.vertexCount ≤ u ∧ u < N ∧
      f.SameCycle 1 (Fin.ofNat N u) ∧ ¬ f.SameCycle 0 (Fin.ofNat N u)) ∨
    (∀ u : ℕ, s.vertexCount ≤ u → u < N → ¬ f.SameCycle 1 (Fin.ofNat N u))

/-- **強化版の存在**: 下界領域では、配置内訳つきの別軌道完成が取れる。
`formula_to_completion` と同じ構成（k₁* 選択・2 ビン詰め・連続区間充填）。 -/
theorem exists_diffCycleData {ℓ : ℕ} [NeZero N] (s : AdvState)
    (hfit : s.Fits N) (hreg : InLowerRegion N ℓ s) (hℓ : 3 ≤ ℓ) :
    Nonempty (DiffCycleData N ℓ s) := by
  classical
  -- 式側の証人から ℓ < N を得る（formula_to_completion と同じ流れ）
  obtain ⟨m0, _, _, hm0lo, hm0hi⟩ := inRegion_formulaSide s hfit hreg hℓ
  have hm0pos : 1 ≤ m0 :=
    le_trans (Nat.le_add_left 1 s.k1) (le_trans (le_max_left _ _) hm0lo)
  have hlt : ℓ < N := by omega
  obtain ⟨hmdvd, hmle⟩ := k1Star_dvd_le (ℓ := ℓ) hlt (by omega)
  set m := PeriodicTM.TwoPointCore.k1Star N ℓ with hm_def
  unfold InLowerRegion at hreg
  have hq3 : s.q + 3 ≤ ℓ := by
    have := lt_of_lt_of_le hreg (min_le_left _ _)
    omega
  have hqm : s.q + 1 ≤ m := by
    have := lt_of_lt_of_le hreg (min_le_right _ _)
    omega
  have hqdef : s.q = s.k0 + s.k1 + s.strays.sum := rfl
  have hvcdef : s.vertexCount
      = 2 + s.k0 + s.k1 + s.strays.sum + s.strays.length := rfl
  obtain ⟨b0, b1, hb0mem, hb1mem, hcover, hp0, hp1, hcross, hc0, hc1, hsum⟩ :=
    exists_packing (ℓ := ℓ) (m := m) s hfit.1 hq3 hqm
  set S0 := (b0.map List.length).sum with hS0
  set S1 := (b1.map List.length).sum with hS1
  set vc := s.vertexCount with hvc
  set n0 := ℓ - 1 - s.k0 - S0 with hn0
  set n1 := m - 1 - s.k1 - S1 with hn1
  set fill0 := List.range' vc n0 with hf0def
  set fill1 := List.range' (vc + n0) n1 with hf1def
  have hf0lo : ∀ x ∈ fill0, vc ≤ x := fun x hx => (List.mem_range'_1.mp hx).1
  have hf1lo : ∀ x ∈ fill1, vc ≤ x := fun x hx => by
    have := (List.mem_range'_1.mp hx).1
    omega
  have hf1hi : ∀ x ∈ fill1, x < vc + n0 + n1 := fun x hx => by
    have := (List.mem_range'_1.mp hx).2
    omega
  have hb0bd : ∀ b ∈ b0, ∀ x ∈ b, 2 + s.k0 + s.k1 ≤ x ∧ x < vc :=
    fun b hb x hx => blocks_mem_bound s (hb0mem b hb) hx
  have hb1bd : ∀ b ∈ b1, ∀ x ∈ b, 2 + s.k0 + s.k1 ≤ x ∧ x < vc :=
    fun b hb x hx => blocks_mem_bound s (hb1mem b hb) hx
  have hb0nd : ∀ b ∈ b0, b.Nodup :=
    fun b hb => strayBlocks_nodup s.strays _ b (hb0mem b hb)
  have hb1nd : ∀ b ∈ b1, b.Nodup :=
    fun b hb => strayBlocks_nodup s.strays _ b (hb1mem b hb)
  have htot : vc + n0 + n1 = ℓ + m := by omega
  have hN : ℓ + m ≤ N := by omega
  have hlen0 : (cycle0Verts s b0 fill0).length = ℓ := by
    rw [cycle0Verts_length, hf0def, List.length_range']
    omega
  have hlen1 : (cycle1Verts s b1 fill1).length = m := by
    rw [cycle1Verts_length, hf1def, List.length_range']
    omega
  have hnd0 := cycle0Verts_nodup s b0 fill0 hb0mem hp0 hb0nd
    List.nodup_range' hf0lo
  have hnd1 := cycle1Verts_nodup s b1 fill1 hb1mem hp1 hb1nd
    List.nodup_range' hf1lo
  have hdisj := cycles_disjoint s b0 b1 fill0 fill1 hb0bd hb1bd
    (fun b hb c hc x hx => hcross b hb c hc hx) hf0lo hf1lo
    (range'_disjoint (by omega))
  have hlt0 : ∀ x ∈ cycle0Verts s b0 fill0, x < N := by
    intro x hx
    rcases mem_cycle0Verts s b0 fill0 hb0bd hf0lo x hx with h | h | h
    · have : 2 + s.k0 ≤ vc := by omega
      omega
    · omega
    · have := (List.mem_range'_1.mp h.2).2
      omega
  have hlt1 : ∀ x ∈ cycle1Verts s b1 fill1, x < N := by
    intro x hx
    rcases mem_cycle1Verts s b1 fill1 hb1bd hf1lo x hx with h | h | h
    · have : 2 + s.k0 + s.k1 ≤ vc := by omega
      rcases h with rfl | h <;> omega
    · omega
    · have := hf1hi x h.2
      omega
  obtain ⟨hcomp, hdiff⟩ :=
    buildPerm_isCompletion s b0 b1 fill0 fill1 hlen0 hlen1 hmdvd hnd0 hnd1
      hdisj hlt0 hlt1 (edges_isAdj s b0 b1 fill0 fill1 hcover)
  -- 配置資源
  have hL0nd := ofNat_injOn (N := N) hlt0 hnd0
  have hL1nd := ofNat_injOn (N := N) hlt1 hnd1
  have hLd := ofNat_disjoint (N := N) hlt0 hlt1 hdisj
  have h1memN : (1 : ℕ) ∈ cycle1Verts s b1 fill1 := by
    unfold cycle1Verts
    simp
  have h1mem : (1 : Fin N) ∈ (cycle1Verts s b1 fill1).map (Fin.ofNat N) := by
    have := List.mem_map_of_mem (f := Fin.ofNat N) h1memN
    rwa [ofNat_one_eq_one (by omega)] at this
  refine ⟨⟨buildPerm N s b0 b1 fill0 fill1, hcomp, hdiff, ?_⟩⟩
  by_cases hn1pos : 1 ≤ n1
  · -- 1 の軌道側の充填ラベル u = vc + n0
    left
    refine ⟨vc + n0, by omega, by omega, ?_, ?_⟩
    · -- u ∈ cycle1 の充填 ⇒ 1 と同一軌道
      have humem : (vc + n0 : ℕ) ∈ cycle1Verts s b1 fill1 := by
        unfold cycle1Verts
        refine List.mem_append.mpr (Or.inr ?_)
        rw [hf1def]
        exact List.mem_range'_1.mpr ⟨le_refl _, by omega⟩
      have humemF : Fin.ofNat N (vc + n0)
          ∈ (cycle1Verts s b1 fill1).map (Fin.ofNat N) :=
        List.mem_map_of_mem humem
      unfold buildPerm
      exact sameCycle_right hL1nd hLd h1mem humemF
    · -- u は 0 の軌道（cycle0）の外
      have hnotin : Fin.ofNat N (vc + n0)
          ∉ (cycle0Verts s b0 fill0).map (Fin.ofNat N) := by
        intro hmem
        obtain ⟨x', hx', heq⟩ := List.mem_map.mp hmem
        have hval : x' % N = (vc + n0) % N := by
          have := congrArg Fin.val heq
          simpa [Fin.ofNat] using this
        rw [Nat.mod_eq_of_lt (hlt0 x' hx'),
          Nat.mod_eq_of_lt (by omega)] at hval
        have humem : (x' : ℕ) ∈ cycle1Verts s b1 fill1 := by
          unfold cycle1Verts
          refine List.mem_append.mpr (Or.inr ?_)
          rw [hf1def, hval]
          exact List.mem_range'_1.mpr ⟨le_refl _, by omega⟩
        exact hdisj hx' humem
      have h0mem : (0 : Fin N)
          ∈ (cycle0Verts s b0 fill0).map (Fin.ofNat N) := by
        have h : (0 : ℕ) ∈ cycle0Verts s b0 fill0 := by
          unfold cycle0Verts
          simp
        have := List.mem_map_of_mem (f := Fin.ofNat N) h
        rwa [ofNat_zero_eq_zero] at this
      unfold buildPerm
      exact not_sameCycle_of_notMem hLd h0mem hnotin
  · -- n1 = 0: 未開示ラベルはすべて 1 の軌道の外
    right
    intro u hu huN hSC
    -- 1 の軌道は cycle1 のリストに閉じる
    have humem : Fin.ofNat N u ∈ (cycle1Verts s b1 fill1).map (Fin.ofNat N) := by
      unfold buildPerm at hSC
      exact sameCycle_mem_of_mem_right hLd h1mem hSC
    -- しかし cycle1 の頂点はすべて vc 未満（n1 = 0 なので充填が無い）
    obtain ⟨x', hx', heq⟩ := List.mem_map.mp humem
    have hval : x' % N = u % N := by
      have := congrArg Fin.val heq
      simpa [Fin.ofNat] using this
    rw [Nat.mod_eq_of_lt (hlt1 x' hx'), Nat.mod_eq_of_lt huN] at hval
    rcases mem_cycle1Verts s b1 fill1 hb1bd hf1lo x' hx' with h | h | h
    · have : 2 + s.k0 + s.k1 ≤ vc := by omega
      rcases h with rfl | h <;> omega
    · omega
    · rw [hf1def] at h
      have := List.mem_range'_1.mp h.2
      omega

end PeriodicTM.ClaimA

#print axioms PeriodicTM.ClaimA.exists_diffCycleData
