/-
FiniteOrderTM/Flip.lean

Track B, milestone M5: the flipped machine as an object.

So far the reversal theory was relational: `KFlipOf M M' σ` says every rule
of `M` has its time-reversed image in `M'`, and `M'` is *given*.  Here we
construct `M'` from `M`.  The construction cannot be computable from the
bare function `M` (one would have to search the rule set), so it is
honestly noncomputable, via choice over a *demand* predicate:

    Demand M q b (p, st')

says some rule of `M` demands, at slot `(q, b)` of the flipped machine, the
reversed rule `(p, st')`.  A `write` rule demands only at the head vector
it wrote; `move` and `perm` rules demand at every head vector.

`KReversible M` is the syntactic reversibility discipline that makes the
demands single-valued:

* `backdet` — demands are unique per slot (backward determinism);
* `move_uniform`, `perm_uniform` — move and permutation rules do not read
  the head vector (the quadruple-format shift discipline).

Main results: under `KReversible M` and an involutive `σ`, the machine
`flipM M σ` is a mutual flip of `M` (`kFlipOf_flipM`,
`kFlipOf_flipM_rev`), hence computes exactly the inverse partial function
(`flipM_tapeSem_inverse`, via `ktapeSem_inverse`).  Note where each
hypothesis is consumed: soundness needed nothing, the relational inverse
needed mutual flips, and only the *existence of the flip as an object*
needs reversibility.
-/
import FiniteOrderTM.Lift

namespace PeriodicTM

open Turing

variable {Γ : Type*} [Inhabited Γ]
variable {Λ : Type*}
variable {ι : Type*}

/-! ### Direction and statement reversal are involutive -/

@[simp] theorem dirRev_dirRev (d : Dir) : dirRev (dirRev d) = d := by
  cases d <;> rfl

@[simp] theorem revMap_revMap (d : ι → Option Dir) :
    revMap (revMap d) = d := by
  funext i
  rcases h : d i with - | dir <;> simp [revMap, h]

/-! ### Demands -/

/-- `Demand M q b v`: some rule of `M` demands, at slot `(q, b)` of the
flipped machine, the reversed rule `v`. -/
inductive Demand (M : KMachine Γ Λ ι) : Λ → (ι → Γ) → Λ × KStmt Γ ι → Prop
  | write {p a q b} :
      M p a = some (q, KStmt.write b) → Demand M q b (p, KStmt.write a)
  | move {p a q d} (b : ι → Γ) :
      M p a = some (q, KStmt.move d) → Demand M q b (p, KStmt.move (revMap d))
  | perm {p a q π} (b : ι → Γ) :
      M p a = some (q, KStmt.perm π) → Demand M q b (p, KStmt.perm π⁻¹)

/-- Syntactic reversibility: demands are single-valued, and move/perm
rules do not read the head vector. -/
structure KReversible (M : KMachine Γ Λ ι) : Prop where
  backdet : ∀ {q b v₁ v₂}, Demand M q b v₁ → Demand M q b v₂ → v₁ = v₂
  move_uniform : ∀ {p a q d}, M p a = some (q, KStmt.move d) →
    ∀ a', M p a' = some (q, KStmt.move d)
  perm_uniform : ∀ {p a q π}, M p a = some (q, KStmt.perm π) →
    ∀ a', M p a' = some (q, KStmt.perm π)

omit [Inhabited Γ] in
/-- **Backward determinism is derived for self-flipped machines**: if `M`
is its own flip under an injective state map, then demands are
single-valued.  Reversibility is therefore not an absent hypothesis of the
soundness theorems but a consequence of flip symmetry plus determinism;
what the soundness theorems genuinely do not need is reversibility as an
*extra* assumption. -/
theorem KFlipOf.self_backdet {M : KMachine Γ Λ ι} {σ : Λ → Λ}
    (hinj : Function.Injective σ) (h : KFlipOf M M σ) :
    ∀ {q b v₁ v₂}, Demand M q b v₁ → Demand M q b v₂ → v₁ = v₂ := by
  intro q b v₁ v₂ h₁ h₂
  have key : ∀ {v}, Demand M q b v → M (σ q) b = some (σ v.1, v.2) := by
    intro v hv
    cases hv with
    | write h₀ => exact h.flip_write _ _ _ _ h₀
    | move b' h₀ => exact h.flip_move _ _ _ _ h₀ b
    | perm b' h₀ => exact h.flip_perm _ _ _ _ h₀ b
  have e := (key h₁).symm.trans (key h₂)
  simp only [Option.some.injEq, Prod.mk.injEq] at e
  obtain ⟨c, T⟩ := v₁
  obtain ⟨c', T'⟩ := v₂
  obtain ⟨e1, e2⟩ := e
  exact Prod.ext (hinj e1) e2

omit [Inhabited Γ] in
/-- An involutory machine's rule set is backward deterministic. -/
theorem KInvolutory.demand_backdet {M : KMachine Γ Λ ι} {σ : Λ → Λ}
    {q₀ qf : Λ} (h : KInvolutory M σ q₀ qf) :
    ∀ {q b v₁ v₂}, Demand M q b v₁ → Demand M q b v₂ → v₁ = v₂ :=
  KFlipOf.self_backdet (Function.LeftInverse.injective h.invol) h.flip

/-! ### The flipped machine -/

open Classical in
/-- The flipped machine: at `(s, b)`, serve the demand placed at
`(σ s, b)`, with the source state pushed through `σ`. -/
noncomputable def flipM (M : KMachine Γ Λ ι) (σ : Λ → Λ) :
    KMachine Γ Λ ι := fun s b =>
  if h : ∃ v, Demand M (σ s) b v then
    some (σ h.choose.1, h.choose.2)
  else none

omit [Inhabited Γ] in
theorem flipM_spec {M : KMachine Γ Λ ι} (hM : KReversible M) {σ : Λ → Λ}
    {s : Λ} {b : ι → Γ} {v : Λ × KStmt Γ ι} (hd : Demand M (σ s) b v) :
    flipM M σ s b = some (σ v.1, v.2) := by
  have hex : ∃ v, Demand M (σ s) b v := ⟨v, hd⟩
  unfold flipM
  rw [dif_pos hex]
  rw [hM.backdet hex.choose_spec hd]

omit [Inhabited Γ] in
theorem flipM_some_inv {M : KMachine Γ Λ ι} {σ : Λ → Λ} {s : Λ}
    {b : ι → Γ} {w : Λ × KStmt Γ ι} (h : flipM M σ s b = some w) :
    ∃ v, Demand M (σ s) b v ∧ w = (σ v.1, v.2) := by
  unfold flipM at h
  by_cases hex : ∃ v, Demand M (σ s) b v
  · rw [dif_pos hex] at h
    exact ⟨hex.choose, hex.choose_spec, (Option.some.inj h).symm⟩
  · rw [dif_neg hex] at h
    cases h

omit [Inhabited Γ] in
theorem flipM_eq_none_iff {M : KMachine Γ Λ ι} {σ : Λ → Λ} {s : Λ}
    {b : ι → Γ} :
    flipM M σ s b = none ↔ ¬ ∃ v, Demand M (σ s) b v := by
  unfold flipM
  by_cases hex : ∃ v, Demand M (σ s) b v
  · rw [dif_pos hex]; simp [hex]
  · rw [dif_neg hex]; simp [hex]

/-! ### The flip is a mutual flip -/

omit [Inhabited Γ] in
/-- Every rule of `M` has its reverse in `flipM M σ`. -/
theorem kFlipOf_flipM {M : KMachine Γ Λ ι} {σ : Λ → Λ}
    (hσ : ∀ q, σ (σ q) = q) (hM : KReversible M) :
    KFlipOf M (flipM M σ) σ := by
  refine ⟨?_, ?_, ?_⟩
  · intro p a q b hrule
    have hd : Demand M (σ (σ q)) b (p, KStmt.write a) := by
      rw [hσ]; exact .write hrule
    exact flipM_spec hM hd
  · intro p a q d hrule b
    have hd : Demand M (σ (σ q)) b (p, KStmt.move (revMap d)) := by
      rw [hσ]; exact .move b hrule
    exact flipM_spec hM hd
  · intro p a q π hrule b
    have hd : Demand M (σ (σ q)) b (p, KStmt.perm π⁻¹) := by
      rw [hσ]; exact .perm b hrule
    exact flipM_spec hM hd

omit [Inhabited Γ] in
/-- Every rule of `flipM M σ` is the reverse of a rule of `M` — this
direction consumes the uniformity of move/perm rules. -/
theorem kFlipOf_flipM_rev {M : KMachine Γ Λ ι} {σ : Λ → Λ}
    (hσ : ∀ q, σ (σ q) = q) (hM : KReversible M) :
    KFlipOf (flipM M σ) M σ := by
  refine ⟨?_, ?_, ?_⟩
  · -- write
    intro p a q b hf
    obtain ⟨v, hd, hw⟩ := flipM_some_inv hf
    cases hd with
    | @write p₀ a₀ _ _ h₀ =>
        simp only [Prod.mk.injEq, KStmt.write.injEq] at hw
        obtain ⟨hq, hb⟩ := hw
        have hp₀ : σ q = p₀ := by rw [hq, hσ]
        rw [hp₀, hb]
        exact h₀
    | move b' h₀ =>
        simp only [Prod.mk.injEq] at hw
        exact absurd hw.2 (by simp)
    | perm b' h₀ =>
        simp only [Prod.mk.injEq] at hw
        exact absurd hw.2 (by simp)
  · -- move
    intro p a q d hf b''
    obtain ⟨v, hd, hw⟩ := flipM_some_inv hf
    cases hd with
    | write h₀ =>
        simp only [Prod.mk.injEq] at hw
        exact absurd hw.2 (by simp)
    | @move p₀ a₀ _ d₀ b' h₀ =>
        simp only [Prod.mk.injEq, KStmt.move.injEq] at hw
        obtain ⟨hq, hdq⟩ := hw
        have hp₀ : σ q = p₀ := by rw [hq, hσ]
        have hrev : revMap d = d₀ := by rw [hdq]; simp
        rw [hp₀, hrev]
        exact hM.move_uniform h₀ b''
    | perm b' h₀ =>
        simp only [Prod.mk.injEq] at hw
        exact absurd hw.2 (by simp)
  · -- perm
    intro p a q π hf b''
    obtain ⟨v, hd, hw⟩ := flipM_some_inv hf
    cases hd with
    | write h₀ =>
        simp only [Prod.mk.injEq] at hw
        exact absurd hw.2 (by simp)
    | move b' h₀ =>
        simp only [Prod.mk.injEq] at hw
        exact absurd hw.2 (by simp)
    | @perm p₀ a₀ _ π₀ b' h₀ =>
        simp only [Prod.mk.injEq, KStmt.perm.injEq] at hw
        obtain ⟨hq, hπq⟩ := hw
        have hp₀ : σ q = p₀ := by rw [hq, hσ]
        have hπ : π⁻¹ = π₀ := by rw [hπq]; simp
        rw [hp₀, hπ]
        exact hM.perm_uniform h₀ b''

/-! ### Inverse semantics for the constructed flip -/

omit [Inhabited Γ] in
/-- Where `flipM` halts: exactly at `σ`-images of states no rule enters. -/
theorem flipM_halt_iff {M : KMachine Γ Λ ι} {σ : Λ → Λ}
    (hσ : ∀ q, σ (σ q) = q) {q₀ : Λ}
    (hent : ∀ q b, (∃ v, Demand M q b v) ↔ q ≠ q₀) :
    ∀ s b, flipM M σ s b = none ↔ s = σ q₀ := by
  intro s b
  rw [flipM_eq_none_iff, hent, not_not]
  constructor
  · intro h
    rw [← hσ s, h]
  · intro h
    rw [h, hσ]

/-- **Milestone M5**: for a syntactically reversible machine, the
constructed flip computes exactly the inverse partial function. -/
theorem flipM_tapeSem_inverse {M : KMachine Γ Λ ι} {σ : Λ → Λ}
    (hσ : ∀ q, σ (σ q) = q) (hM : KReversible M) {q₀ qf : Λ}
    (hhalt : ∀ q a, M q a = none ↔ q = qf)
    (hent : ∀ q b, (∃ v, Demand M q b v) ↔ q ≠ q₀)
    {T T' : ι → Tape Γ} :
    T' ∈ ktapeSem M q₀ T ↔ T ∈ ktapeSem (flipM M σ) (σ qf) T' :=
  ktapeSem_inverse hσ (kFlipOf_flipM hσ hM) (kFlipOf_flipM_rev hσ hM)
    hhalt (flipM_halt_iff hσ hent)

/-! ### Flip distributes over liftL (M7 ingredient) -/

/-- Flipping distributes over left-bank lifting: the flip of `liftL R` is
`liftL` of the flip of `R`, with the same state map. -/
theorem kFlipOf_liftL {R R' : KMachine Γ Λ ι} {σ : Λ → Λ}
    (h : KFlipOf R R' σ) :
    KFlipOf (liftL R (κ := κ)) (liftL R' (κ := κ)) σ := by
  refine ⟨?_, ?_, ?_⟩
  -- flip_write ---------------------------------------------------------------
  · intro p a q b hrule
    simp only [liftL] at hrule
    rcases eR : R p (a ∘ Sum.inl) with _ | ⟨q', st'⟩
    · simp [eR] at hrule
    · rw [eR, Option.map_some] at hrule
      obtain ⟨hq, hst⟩ := Prod.mk.injEq .. ▸ Option.some.inj hrule
      subst hq
      cases st' with
      | write b' =>
        simp only [KStmt.inflate] at hst
        -- hst : KStmt.write (Sum.elim b' (a ∘ Sum.inr)) = KStmt.write b
        have heq : Sum.elim b' (a ∘ Sum.inr) = b := KStmt.write.inj hst
        have hbl : b ∘ Sum.inl = b' :=
          funext fun i => (congr_fun heq (Sum.inl i)).symm
        have hbr : b ∘ Sum.inr = a ∘ Sum.inr :=
          funext fun j => (congr_fun heq (Sum.inr j)).symm
        simp only [liftL, hbl, h.flip_write p (a ∘ Sum.inl) q' b' eR,
                   Option.map_some, KStmt.inflate]
        congr 2; congr 1; funext i; rcases i with il | ir
        · rfl
        · exact congr_fun hbr ir
      | move d  => simp [KStmt.inflate] at hst
      | perm π  => simp [KStmt.inflate] at hst
  -- flip_move ----------------------------------------------------------------
  · intro p a q d hrule bb
    simp only [liftL] at hrule
    rcases eR : R p (a ∘ Sum.inl) with _ | ⟨q', st'⟩
    · simp [eR] at hrule
    · rw [eR, Option.map_some] at hrule
      obtain ⟨hq, hst⟩ := Prod.mk.injEq .. ▸ Option.some.inj hrule
      subst hq
      cases st' with
      | write b' => simp [KStmt.inflate] at hst
      | move d' =>
        simp only [KStmt.inflate] at hst
        -- hst : KStmt.move (Sum.elim d' (fun _ => none)) = KStmt.move d
        have heq : Sum.elim d' (fun _ => none) = d := KStmt.move.inj hst
        simp only [liftL, h.flip_move p (a ∘ Sum.inl) q' d' eR (bb ∘ Sum.inl),
                   Option.map_some, KStmt.inflate]
        congr 2; congr 1; funext i; rcases i with il | ir
        · simp [revMap, ← congr_fun heq (Sum.inl il)]
        · simp [revMap, ← congr_fun heq (Sum.inr ir)]
      | perm π  => simp [KStmt.inflate] at hst
  -- flip_perm ----------------------------------------------------------------
  · intro p a q π hrule bb
    simp only [liftL] at hrule
    rcases eR : R p (a ∘ Sum.inl) with _ | ⟨q', st'⟩
    · simp [eR] at hrule
    · rw [eR, Option.map_some] at hrule
      obtain ⟨hq, hst⟩ := Prod.mk.injEq .. ▸ Option.some.inj hrule
      subst hq
      cases st' with
      | write b' => simp [KStmt.inflate] at hst
      | move d   => simp [KStmt.inflate] at hst
      | perm π' =>
        simp only [KStmt.inflate] at hst
        -- hst : KStmt.perm (Equiv.sumCongr π' (Equiv.refl κ)) = KStmt.perm π
        have heq : Equiv.sumCongr π' (Equiv.refl κ) = π := KStmt.perm.inj hst
        simp only [liftL, h.flip_perm p (a ∘ Sum.inl) q' π' eR (bb ∘ Sum.inl),
                   Option.map_some, KStmt.inflate, ← heq]
        refine congrArg some (Prod.ext rfl ?_)
        exact congrArg KStmt.perm (Equiv.ext fun x => by cases x <;> simp)

/-- Left-bank lifting preserves syntactic reversibility. -/
theorem liftL_reversible {R : KMachine Γ Λ ι} (hR : KReversible R) :
    KReversible (liftL R (κ := κ)) where
  backdet := by
    intro q b v₁ v₂ h₁ h₂
    -- Unpack a liftL demand to an R rule; cross-constructor cases are impossible
    -- via hR.backdet since write/move/perm are disjoint.
    cases h₁ with
    | write e₁ =>
      simp only [liftL] at e₁
      obtain ⟨⟨q₁', st₁'⟩, eR₁, hrule₁⟩ := Option.map_eq_some_iff.mp e₁
      dsimp only at hrule₁
      obtain ⟨hq₁, hst₁⟩ := Prod.mk.injEq .. ▸ hrule₁; rw [hq₁] at eR₁
      cases st₁' with
      | move _ | perm _ => simp [KStmt.inflate] at hst₁
      | write b₁' =>
        simp only [KStmt.inflate] at hst₁
        have heq₁ := KStmt.write.inj hst₁
        have hbL₁ : b₁' = b ∘ Sum.inl := funext fun i => congr_fun heq₁ (Sum.inl i)
        have haR₁ : _ ∘ Sum.inr = b ∘ Sum.inr := funext fun j => congr_fun heq₁ (Sum.inr j)
        subst hbL₁
        have hd₁ : Demand R q (b ∘ Sum.inl) (_, KStmt.write (_ ∘ Sum.inl)) := .write eR₁
        cases h₂ with
        | write e₂ =>
          simp only [liftL] at e₂
          obtain ⟨⟨q₂', st₂'⟩, eR₂, hrule₂⟩ := Option.map_eq_some_iff.mp e₂
          dsimp only at hrule₂
          obtain ⟨hq₂, hst₂⟩ := Prod.mk.injEq .. ▸ hrule₂; rw [hq₂] at eR₂
          cases st₂' with
          | move _ | perm _ => simp [KStmt.inflate] at hst₂
          | write b₂' =>
            simp only [KStmt.inflate] at hst₂
            have heq₂ := KStmt.write.inj hst₂
            have hbL₂ : b₂' = b ∘ Sum.inl := funext fun i => congr_fun heq₂ (Sum.inl i)
            have haR₂ : _ ∘ Sum.inr = b ∘ Sum.inr := funext fun j => congr_fun heq₂ (Sum.inr j)
            subst hbL₂
            have hd₂ : Demand R q (b ∘ Sum.inl) (_, KStmt.write (_ ∘ Sum.inl)) := .write eR₂
            obtain ⟨hp, hst⟩ := Prod.mk.injEq .. ▸ hR.backdet hd₁ hd₂
            have haL := KStmt.write.inj hst
            simp only [Prod.mk.injEq]; refine ⟨hp, ?_⟩; congr 1; funext i; rcases i with il | ir
            · exact congr_fun haL il
            · exact (congr_fun haR₁ ir).trans (congr_fun haR₂ ir).symm
        | move _ e₂ =>
          simp only [liftL] at e₂
          obtain ⟨⟨q₂', st₂'⟩, eR₂, hrule₂⟩ := Option.map_eq_some_iff.mp e₂
          dsimp only at hrule₂
          obtain ⟨hq₂, hst₂⟩ := Prod.mk.injEq .. ▸ hrule₂; rw [hq₂] at eR₂
          cases st₂' with
          | write _ | perm _ => simp [KStmt.inflate] at hst₂
          | move d₂' =>
            simp only [KStmt.inflate] at hst₂
            have hd₂ : Demand R q (b ∘ Sum.inl) (_, KStmt.move (revMap d₂')) := .move (b ∘ Sum.inl) eR₂
            have := hR.backdet hd₁ hd₂; simp at this
        | perm _ e₂ =>
          simp only [liftL] at e₂
          obtain ⟨⟨q₂', st₂'⟩, eR₂, hrule₂⟩ := Option.map_eq_some_iff.mp e₂
          dsimp only at hrule₂
          obtain ⟨hq₂, hst₂⟩ := Prod.mk.injEq .. ▸ hrule₂; rw [hq₂] at eR₂
          cases st₂' with
          | write _ | move _ => simp [KStmt.inflate] at hst₂
          | perm π₂' =>
            simp only [KStmt.inflate] at hst₂
            have hd₂ : Demand R q (b ∘ Sum.inl) (_, KStmt.perm π₂'⁻¹) := .perm (b ∘ Sum.inl) eR₂
            have := hR.backdet hd₁ hd₂; simp at this
    | move _ e₁ =>
      simp only [liftL] at e₁
      obtain ⟨⟨q₁', st₁'⟩, eR₁, hrule₁⟩ := Option.map_eq_some_iff.mp e₁
      dsimp only at hrule₁
      obtain ⟨hq₁, hst₁⟩ := Prod.mk.injEq .. ▸ hrule₁; rw [hq₁] at eR₁
      cases st₁' with
      | write _ | perm _ => simp [KStmt.inflate] at hst₁
      | move d₁' =>
        simp only [KStmt.inflate] at hst₁
        have heq₁ := KStmt.move.inj hst₁
        have hd₁ : Demand R q (b ∘ Sum.inl) (_, KStmt.move (revMap d₁')) := .move (b ∘ Sum.inl) eR₁
        cases h₂ with
        | write e₂ =>
          simp only [liftL] at e₂
          obtain ⟨⟨q₂', st₂'⟩, eR₂, hrule₂⟩ := Option.map_eq_some_iff.mp e₂
          dsimp only at hrule₂
          obtain ⟨hq₂, hst₂⟩ := Prod.mk.injEq .. ▸ hrule₂; rw [hq₂] at eR₂
          cases st₂' with
          | move _ | perm _ => simp [KStmt.inflate] at hst₂
          | write b₂' =>
            simp only [KStmt.inflate] at hst₂
            have hbL₂ : b₂' = b ∘ Sum.inl :=
              funext fun i => congr_fun (KStmt.write.inj hst₂) (Sum.inl i)
            subst hbL₂
            have hd₂ : Demand R q (b ∘ Sum.inl) (_, KStmt.write (_ ∘ Sum.inl)) := .write eR₂
            have := hR.backdet hd₁ hd₂; simp at this
        | move _ e₂ =>
          simp only [liftL] at e₂
          obtain ⟨⟨q₂', st₂'⟩, eR₂, hrule₂⟩ := Option.map_eq_some_iff.mp e₂
          dsimp only at hrule₂
          obtain ⟨hq₂, hst₂⟩ := Prod.mk.injEq .. ▸ hrule₂; rw [hq₂] at eR₂
          cases st₂' with
          | write _ | perm _ => simp [KStmt.inflate] at hst₂
          | move d₂' =>
            simp only [KStmt.inflate] at hst₂
            have heq₂ := KStmt.move.inj hst₂
            have hd₂ : Demand R q (b ∘ Sum.inl) (_, KStmt.move (revMap d₂')) := .move (b ∘ Sum.inl) eR₂
            obtain ⟨hp, hst⟩ := Prod.mk.injEq .. ▸ hR.backdet hd₁ hd₂
            have hd' : d₁' = d₂' := by
              have h := KStmt.move.inj hst  -- revMap d₁' = revMap d₂'
              calc d₁' = revMap (revMap d₁') := (revMap_revMap d₁').symm
                   _ = revMap (revMap d₂') := by rw [h]
                   _ = d₂' := revMap_revMap d₂'
            congr 1; rw [← heq₁, ← heq₂, hd']
        | perm _ e₂ =>
          simp only [liftL] at e₂
          obtain ⟨⟨q₂', st₂'⟩, eR₂, hrule₂⟩ := Option.map_eq_some_iff.mp e₂
          dsimp only at hrule₂
          obtain ⟨hq₂, hst₂⟩ := Prod.mk.injEq .. ▸ hrule₂; rw [hq₂] at eR₂
          cases st₂' with
          | write _ | move _ => simp [KStmt.inflate] at hst₂
          | perm π₂' =>
            simp only [KStmt.inflate] at hst₂
            have hd₂ : Demand R q (b ∘ Sum.inl) (_, KStmt.perm π₂'⁻¹) := .perm (b ∘ Sum.inl) eR₂
            have := hR.backdet hd₁ hd₂; simp at this
    | perm _ e₁ =>
      simp only [liftL] at e₁
      obtain ⟨⟨q₁', st₁'⟩, eR₁, hrule₁⟩ := Option.map_eq_some_iff.mp e₁
      dsimp only at hrule₁
      obtain ⟨hq₁, hst₁⟩ := Prod.mk.injEq .. ▸ hrule₁; rw [hq₁] at eR₁
      cases st₁' with
      | write _ | move _ => simp [KStmt.inflate] at hst₁
      | perm π₁' =>
        simp only [KStmt.inflate] at hst₁
        have heq₁ := KStmt.perm.inj hst₁
        have hd₁ : Demand R q (b ∘ Sum.inl) (_, KStmt.perm π₁'⁻¹) := .perm (b ∘ Sum.inl) eR₁
        cases h₂ with
        | write e₂ =>
          simp only [liftL] at e₂
          obtain ⟨⟨q₂', st₂'⟩, eR₂, hrule₂⟩ := Option.map_eq_some_iff.mp e₂
          dsimp only at hrule₂
          obtain ⟨hq₂, hst₂⟩ := Prod.mk.injEq .. ▸ hrule₂; rw [hq₂] at eR₂
          cases st₂' with
          | move _ | perm _ => simp [KStmt.inflate] at hst₂
          | write b₂' =>
            simp only [KStmt.inflate] at hst₂
            have hbL₂ : b₂' = b ∘ Sum.inl :=
              funext fun i => congr_fun (KStmt.write.inj hst₂) (Sum.inl i)
            subst hbL₂
            have hd₂ : Demand R q (b ∘ Sum.inl) (_, KStmt.write (_ ∘ Sum.inl)) := .write eR₂
            have := hR.backdet hd₁ hd₂; simp at this
        | move _ e₂ =>
          simp only [liftL] at e₂
          obtain ⟨⟨q₂', st₂'⟩, eR₂, hrule₂⟩ := Option.map_eq_some_iff.mp e₂
          dsimp only at hrule₂
          obtain ⟨hq₂, hst₂⟩ := Prod.mk.injEq .. ▸ hrule₂; rw [hq₂] at eR₂
          cases st₂' with
          | write _ | perm _ => simp [KStmt.inflate] at hst₂
          | move d₂' =>
            simp only [KStmt.inflate] at hst₂
            have hd₂ : Demand R q (b ∘ Sum.inl) (_, KStmt.move (revMap d₂')) := .move (b ∘ Sum.inl) eR₂
            have := hR.backdet hd₁ hd₂; simp at this
        | perm _ e₂ =>
          simp only [liftL] at e₂
          obtain ⟨⟨q₂', st₂'⟩, eR₂, hrule₂⟩ := Option.map_eq_some_iff.mp e₂
          dsimp only at hrule₂
          obtain ⟨hq₂, hst₂⟩ := Prod.mk.injEq .. ▸ hrule₂; rw [hq₂] at eR₂
          cases st₂' with
          | write _ | move _ => simp [KStmt.inflate] at hst₂
          | perm π₂' =>
            simp only [KStmt.inflate] at hst₂
            have heq₂ := KStmt.perm.inj hst₂
            have hd₂ : Demand R q (b ∘ Sum.inl) (_, KStmt.perm π₂'⁻¹) := .perm (b ∘ Sum.inl) eR₂
            obtain ⟨hp, hst⟩ := Prod.mk.injEq .. ▸ hR.backdet hd₁ hd₂
            have hπ' : π₁' = π₂' := by
              have h := KStmt.perm.inj hst  -- π₁'⁻¹ = π₂'⁻¹
              calc π₁' = π₁'⁻¹⁻¹ := (inv_inv π₁').symm
                   _ = π₂'⁻¹⁻¹ := by rw [h]
                   _ = π₂' := inv_inv π₂'
            congr 1; rw [← heq₁, ← heq₂, hπ']
  move_uniform := by
    intro p a q d hrule a'
    simp only [liftL] at hrule ⊢
    rcases eR : R p (a ∘ Sum.inl) with _ | ⟨q', st'⟩
    · simp [eR] at hrule
    · rw [eR, Option.map_some] at hrule
      obtain ⟨hq, hst⟩ := Prod.mk.injEq .. ▸ Option.some.inj hrule
      subst hq
      cases st' with
      | write b' => simp [KStmt.inflate] at hst
      | move d' =>
        rw [hR.move_uniform eR (a' ∘ Sum.inl), Option.map_some, KStmt.inflate] at *
        exact hst ▸ rfl
      | perm π   => simp [KStmt.inflate] at hst
  perm_uniform := by
    intro p a q π hrule a'
    simp only [liftL] at hrule ⊢
    rcases eR : R p (a ∘ Sum.inl) with _ | ⟨q', st'⟩
    · simp [eR] at hrule
    · rw [eR, Option.map_some] at hrule
      obtain ⟨hq, hst⟩ := Prod.mk.injEq .. ▸ Option.some.inj hrule
      subst hq
      cases st' with
      | write b' => simp [KStmt.inflate] at hst
      | move d   => simp [KStmt.inflate] at hst
      | perm π' =>
        rw [hR.perm_uniform eR (a' ∘ Sum.inl), Option.map_some, KStmt.inflate] at *
        exact hst ▸ rfl

/-- liftL preserves the unique-halt condition. -/
theorem liftL_halt_iff {R : KMachine Γ Λ ι} {qf : Λ}
    (hRhalt : ∀ q a, R q a = none ↔ q = qf) (q : Λ) (a : ι ⊕ κ → Γ) :
    (liftL R (κ := κ)) q a = none ↔ q = qf := by
  simp only [liftL, Option.map_eq_none_iff, hRhalt]

/-- liftL preserves the entry condition: a state is demanded (at left-bank
heads b ∘ Sum.inl) iff it is demanded on the full 2-bank head vector b.

Direction ←: given Demand R₀ at left heads, extend to a 2-bank demand.
Direction →: given Demand (liftL R) at b, project to Demand R at b ∘ Sum.inl. -/
theorem liftL_demand_iff {R : KMachine Γ Λ ι} {q0 : Λ}
    (hRent : ∀ q b, (∃ v, Demand R q b v) ↔ q ≠ q0) :
    ∀ q (b : ι ⊕ κ → Γ), (∃ v, Demand (liftL R (κ := κ)) q b v) ↔ q ≠ q0 := by
  intro q b
  constructor
  · rintro ⟨v, hv⟩
    -- project demand to left-bank
    have : ∃ v₀, Demand R q (b ∘ Sum.inl) v₀ := by
      cases hv with
      | write e =>
        -- (liftL R) p a = some (q, KStmt.write b)
        simp only [liftL] at e
        rename_i p₀ a₀
        rcases eR : R p₀ (a₀ ∘ Sum.inl) with _ | ⟨q', st'⟩
        · simp [eR] at e
        · rw [eR, Option.map_some] at e
          obtain ⟨hq, hst⟩ := Prod.mk.injEq .. ▸ Option.some.inj e
          subst hq
          cases st' with
          | write b' =>
            simp only [KStmt.inflate] at hst
            have hb' : b' = b ∘ Sum.inl := funext fun i =>
              congr_fun (KStmt.write.inj hst) (Sum.inl i)
            exact ⟨_, Demand.write (hb' ▸ eR)⟩
          | move d   => simp [KStmt.inflate] at hst
          | perm π   => simp [KStmt.inflate] at hst
      | move _ e_rule =>
        simp only [liftL] at e_rule
        obtain ⟨⟨q', st'⟩, eR, hrule⟩ := Option.map_eq_some_iff.mp e_rule
        dsimp only at hrule
        obtain ⟨hq, hst⟩ := Prod.mk.injEq .. ▸ hrule; rw [hq] at eR
        cases st' with
        | write b' => simp [KStmt.inflate] at hst
        | move d'  => exact ⟨_, Demand.move (b ∘ Sum.inl) eR⟩
        | perm π   => simp [KStmt.inflate] at hst
      | perm _ e_rule =>
        simp only [liftL] at e_rule
        obtain ⟨⟨q', st'⟩, eR, hrule⟩ := Option.map_eq_some_iff.mp e_rule
        dsimp only at hrule
        obtain ⟨hq, hst⟩ := Prod.mk.injEq .. ▸ hrule; rw [hq] at eR
        cases st' with
        | write b' => simp [KStmt.inflate] at hst
        | move d   => simp [KStmt.inflate] at hst
        | perm π'  => exact ⟨_, Demand.perm (b ∘ Sum.inl) eR⟩
    exact (hRent q (b ∘ Sum.inl)).mp this
  · intro hq
    -- lift a demand of R at left-bank heads to a demand of liftL R
    obtain ⟨v₀, hv₀⟩ := (hRent q (b ∘ Sum.inl)).mpr hq
    cases hv₀ with
    | write eR =>
      rename_i p₀ a₀
      refine ⟨_, Demand.write (p := p₀) (a := Sum.elim a₀ (b ∘ Sum.inr)) ?_⟩
      simp only [liftL, Sum.elim_comp_inl, eR, Option.map_some, KStmt.inflate]
      simp only [Option.some.injEq, Prod.mk.injEq]; refine ⟨trivial, ?_⟩
      congr 1; funext (i : ι ⊕ κ); rcases i with il | ir <;> simp
    | move _ eR =>
      rename_i p_state p_tape d_dir
      have h_move : (liftL R (κ := κ)) p_state (Sum.elim p_tape (b ∘ Sum.inr)) =
          some (q, KStmt.move (Sum.elim d_dir fun _ => none)) :=
        by simp only [liftL, Sum.elim_comp_inl, eR, Option.map_some, KStmt.inflate]
      exact ⟨_, Demand.move b h_move⟩
    | perm _ eR =>
      rename_i p_state p_tape pi_val
      have h_perm : (liftL R (κ := κ)) p_state (Sum.elim p_tape (b ∘ Sum.inr)) =
          some (q, KStmt.perm (Equiv.sumCongr pi_val (Equiv.refl κ))) :=
        by simp only [liftL, Sum.elim_comp_inl, eR, Option.map_some, KStmt.inflate]
      exact ⟨_, Demand.perm b h_perm⟩

end PeriodicTM
