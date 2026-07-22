/-
FiniteOrderTM/NoGo.lean

Pre-period-2 no-go (ROADMAP Track A, A2–A3).

**Mathematical content**:

A2. *Pre-period-two is hard.*  There exists a computable (2,1)-periodic
    function f : ℕ → ℕ (f³ = f² but f² ≠ f) whose image is Σ₁-complete,
    hence not computable.

A3. *Decidability separation.*  For every computable (1,p)-periodic f the
    image equals Fix(f^p), which is decidable.  At pre-period m = 2 the
    image can be Σ₁-complete.

**The halting-tail function** (witness for A2):

  haltingTail x =
    0           if x is odd  ("b_n → sink")
    0           if x = 2*(Nat.pair n s) and evaln s (ofNatCode n) 0 = none
    2n+1        if x = 2*(Nat.pair n s) and evaln s (ofNatCode n) 0 = some _

  Key properties proved:
  * Computable (step-bounded simulation, primitive recursive building blocks).
  * f² ≡ 0: every output of f is 0 or 2k+1 (odd), and f(0) = 0, f(2k+1) = 0.
  * f³ = f² trivially (f² = const 0).
  * f² ≠ f: x = 2 (= 2*Nat.pair 0 1); evaln 1 Code.zero 0 = some 0,
      so f(2) = 1 ≠ 0 = f²(2).
  * range(f) ⊇ {2n+1 | (ofNatCode n).eval 0 halts}, so range(f) is
      Σ₁-complete (≥ halting problem via ofNatCode bijection).
-/
import Mathlib.Computability.Halting
import Mathlib.Data.Set.Function

namespace PeriodicTM

open Set Nat.Partrec Nat.Partrec.Code

/-! ### Algebraic lemma: range of an idempotent equals its fixpoints -/

/-- The image of an idempotent function equals its set of fixpoints. -/
theorem range_idempotent_eq_fixpoints {α : Type*} {f : α → α}
    (hf : ∀ x, f (f x) = f x) : range f = {x | f x = x} := by
  ext x; simp only [mem_range, mem_setOf_eq]
  exact ⟨fun ⟨y, hy⟩ => hy ▸ hf y, fun hx => ⟨x, hx⟩⟩

/-! ### Decidability lemma: fixpoints of a computable function are decidable -/

/-- If f : ℕ → ℕ is computable, the predicate "f x = x" is decidable by a
computable procedure.  Together with `range_idempotent_eq_fixpoints`, this shows
that pre-period ≤ 1 implies decidable image (decidability separation, A3). -/
theorem computablePred_fix_of_computable {f : ℕ → ℕ} (hf : Computable f) :
    ComputablePred (fun x => f x = x) := by
  apply Computable.computablePred
  obtain ⟨_, heq⟩ := Primrec.eq (α := ℕ)
  exact (heq.to_comp.comp (hf.pair .id)).of_eq fun x => by simp [id]

/-- The image of a computable idempotent is decidable. -/
theorem computablePred_range_of_computable_idempotent {f : ℕ → ℕ}
    (hf : Computable f) (hidm : ∀ x, f (f x) = f x) :
    ComputablePred (fun x => x ∈ range f) := by
  simp_rw [range_idempotent_eq_fixpoints hidm, mem_setOf_eq]
  exact computablePred_fix_of_computable hf

/-! ### The halting-tail function -/

/-- `ofNatCode : ℕ → Code` is computable; it is the decode map of the
`Encodable Code` instance, satisfying `Encodable.decode n = some (ofNatCode n)`. -/
theorem computable_ofNatCode : Computable ofNatCode :=
  (Primrec.decode.to_comp.option_getD (Computable.const Nat.Partrec.Code.zero)).of_eq fun n => by
    simp [Encodable.decode]

/-- The halting-tail function.
  - Odd inputs (2k+1): mapped to 0 (sink).
  - Even inputs 2*(Nat.pair n s): simulate code n for s steps on 0;
      return 2n+1 if it halts, 0 otherwise.
  - 0 is even with s=0, evaln 0 ... = none, returning 0. -/
def haltingTail : ℕ → ℕ := fun x =>
  if x.bodd then 0
  else (evaln ((x / 2).unpair.2) (ofNatCode ((x / 2).unpair.1)) 0).elim 0
        (fun _ => 2 * (x / 2).unpair.1 + 1)

private theorem haltingTail_odd (k : ℕ) : haltingTail (2 * k + 1) = 0 := by
  simp [haltingTail, Nat.bodd_mul]

private theorem haltingTail_image (x : ℕ) :
    haltingTail x = 0 ∨ ∃ n, haltingTail x = 2 * n + 1 := by
  simp only [haltingTail]
  split_ifs
  · exact Or.inl rfl
  · cases evaln ((x / 2).unpair.2) (ofNatCode ((x / 2).unpair.1)) 0 with
    | none => exact Or.inl rfl
    | some _ => exact Or.inr ⟨_, rfl⟩

private theorem haltingTail_zero_val : haltingTail 0 = 0 := by
  simp [haltingTail, Nat.bodd_zero,
        show evaln 0 (ofNatCode 0) 0 = (Option.none : Option ℕ) from by simp [evaln]]

/-- f²(x) = 0 for all x: f maps everything to 0 or an odd number, both map to 0. -/
theorem haltingTail_sq (x : ℕ) : haltingTail (haltingTail x) = 0 := by
  rcases haltingTail_image x with h | ⟨n, h⟩
  · rw [h]; exact haltingTail_zero_val
  · rw [h]; exact haltingTail_odd n

/-- f³ = f²: both are constantly 0. -/
theorem haltingTail_cube (x : ℕ) :
    haltingTail (haltingTail (haltingTail x)) = haltingTail (haltingTail x) := by
  rw [haltingTail_sq (haltingTail x), haltingTail_sq x]

/-- haltingTail 2 = 1: x=2 is even, 2/2=1, unpair 1 = (0,1), ofNatCode 0 = zero,
evaln 1 zero 0 = some 0, result = 2*0+1 = 1. -/
private theorem haltingTail_two : haltingTail 2 = 1 := by
  simp only [haltingTail, show (2 : ℕ).bodd = false from by decide,
             Bool.false_eq_true, ite_false, show (2 : ℕ) / 2 = 1 from by decide,
             show Nat.unpair 1 = (0, 1) from by decide]
  rw [show ofNatCode 0 = Nat.Partrec.Code.zero from by simp [ofNatCode]]
  rw [show evaln 1 Nat.Partrec.Code.zero 0 = some 0 from by simp [evaln]]
  rfl

/-- Witness that f² ≠ f: x = 2, where f(2) = 1 but f²(2) = 0. -/
theorem haltingTail_sq_ne_self :
    ∃ x : ℕ, haltingTail (haltingTail x) ≠ haltingTail x :=
  ⟨2, by rw [haltingTail_sq, haltingTail_two]; exact Nat.zero_ne_one⟩

/-- 2n+1 ∈ range(haltingTail) iff code n halts on 0. -/
theorem mem_range_haltingTail_iff (n : ℕ) :
    2 * n + 1 ∈ range haltingTail ↔ (Nat.Partrec.Code.eval (ofNatCode n) 0).Dom := by
  constructor
  · rintro ⟨x, hx⟩
    simp only [haltingTail] at hx
    by_cases hodd : x.bodd = true
    · simp [hodd] at hx
    · simp only [hodd] at hx
      rcases h : evaln ((x / 2).unpair.2) (ofNatCode ((x / 2).unpair.1)) 0 with _ | v
      · rw [h] at hx; simp at hx
      · rw [h] at hx
        -- (some v).elim 0 f = f v is rfl; so hx becomes 2*(x/2).unpair.1+1 = 2*n+1
        change 2 * (x / 2).unpair.1 + 1 = 2 * n + 1 at hx
        have hn : (x / 2).unpair.1 = n := by omega
        rw [← hn]; exact (evaln_sound h).choose
  · intro hdom
    set v := (Nat.Partrec.Code.eval (ofNatCode n) 0).get hdom
    obtain ⟨k, hk⟩ := evaln_complete.mp (show v ∈ Nat.Partrec.Code.eval (ofNatCode n) 0
                                           from ⟨hdom, rfl⟩)
    exact ⟨2 * Nat.pair n k, by
      simp only [haltingTail, Nat.bodd_mul]
      rw [show 2 * Nat.pair n k / 2 = Nat.pair n k from by omega, Nat.unpair_pair,
          show evaln k (ofNatCode n) 0 = some v from hk]; rfl⟩

/-- haltingTail is computable.  All building blocks are primitive recursive
(or Computable for ofNatCode); see proof for the explicit Primrec composition. -/
theorem computable_haltingTail : Computable haltingTail := by
  have hn_prim : Primrec (fun x : ℕ => x.div2.unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.nat_div2)
  have hs_prim : Primrec (fun x : ℕ => x.div2.unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp Primrec.nat_div2)
  have hcode : Computable (fun x : ℕ => ofNatCode x.div2.unpair.1) :=
    computable_ofNatCode.comp hn_prim.to_comp
  -- Pack into the argument type of primrec_evaln: (ℕ × Code) × ℕ
  have harg : Computable (fun x : ℕ =>
      ((x.div2.unpair.2, ofNatCode x.div2.unpair.1), (0 : ℕ))) :=
    (hs_prim.to_comp.pair hcode).pair (Computable.const 0)
  have heval : Computable (fun x : ℕ =>
      evaln x.div2.unpair.2 (ofNatCode x.div2.unpair.1) 0) :=
    (primrec_evaln.to_comp.comp harg).of_eq fun x => rfl
  have h2n1 : Primrec (fun x : ℕ => 2 * x.div2.unpair.1 + 1) :=
    Primrec₂.comp Primrec.nat_add
      (Primrec₂.comp Primrec.nat_mul (Primrec.const 2) hn_prim)
      (Primrec.const 1)
  -- Option.elim: use option_casesOn then convert (elim and casesOn are propositionally equal)
  have helim : Computable (fun x : ℕ =>
      (evaln x.div2.unpair.2 (ofNatCode x.div2.unpair.1) 0).elim 0
        (fun _ => 2 * x.div2.unpair.1 + 1)) :=
    (Computable.option_casesOn heval (Computable.const 0)
      (show Computable₂ (fun (x : ℕ) (_ : ℕ) => 2 * x.div2.unpair.1 + 1) from
        (h2n1.comp Primrec.fst).to_comp)).of_eq fun x => by
      cases evaln x.div2.unpair.2 (ofNatCode x.div2.unpair.1) 0 <;> rfl
  -- Bool-if vs bif: `if b then t else f` for b : Bool is `if b=true then t else f`;
  -- `bif b then t else f` is Bool.casesOn. They're NOT defeq; use of_eq to convert.
  have hcond : Computable (fun x : ℕ =>
      bif x.bodd then 0 else
        (evaln x.div2.unpair.2 (ofNatCode x.div2.unpair.1) 0).elim 0
          (fun _ => 2 * x.div2.unpair.1 + 1)) :=
    Computable.cond Primrec.nat_bodd.to_comp (Computable.const 0) helim
  exact hcond.of_eq fun x => by simp only [haltingTail, Nat.div2_val]; cases x.bodd <;> simp

/-! ### Pre-period-2 no-go theorem -/

/-- **Pre-period-2 no-go (ROADMAP A2)**.

The halting-tail function witnesses:
1. Computable: proved via primitive-recursive building blocks (`computable_haltingTail`).
2. f³ = f²: both are constantly 0 (`haltingTail_cube`).
3. f² ≠ f: x = 2 witnesses f(2) = 1 ≠ 0 = f²(2).
4. range undecidable: 2n+1 ∈ range(f) ↔ (ofNatCode n).eval 0 halts.
   If the range were computable, so would `fun n => (ofNatCode n).eval 0 Dom`.
   Since `ofNatCode` is a bijection (inverse: Encodable.encode), this gives
   a decision procedure for `fun c : Code => c.eval 0 Dom`, contradicting
   `ComputablePred.halting_problem 0`. -/
theorem preperiod_two_nogo :
    ∃ f : ℕ → ℕ,
      Computable f ∧
      (∀ x, f (f (f x)) = f (f x)) ∧
      (∃ x, f (f x) ≠ f x) ∧
      ¬ ComputablePred (fun x => x ∈ range f) := by
  refine ⟨haltingTail, computable_haltingTail, haltingTail_cube, haltingTail_sq_ne_self, ?_⟩
  intro hrange
  obtain ⟨_, hrange_c⟩ := hrange
  -- Compose with n ↦ 2n+1 to get decidability for odd members of range
  have hmul2 : Computable (fun n : ℕ => 2 * n + 1) :=
    (Primrec₂.comp Primrec.nat_add
      (Primrec₂.comp Primrec.nat_mul (Primrec.const 2) .id)
      (Primrec.const 1)).to_comp
  have hrange_odd : ComputablePred (fun n : ℕ => 2 * n + 1 ∈ range haltingTail) :=
    ⟨inferInstance, (hrange_c.comp hmul2).of_eq fun n => rfl⟩
  -- Convert via range membership criterion to get decidability for halting-on-ℕ
  have hhalting_n : ComputablePred (fun n : ℕ => (Nat.Partrec.Code.eval (ofNatCode n) 0).Dom) :=
    hrange_odd.of_eq fun n => mem_range_haltingTail_iff n
  -- Transport from ℕ to Code via the Encodable bijection ofNatCode / Encodable.encode
  obtain ⟨hdec_n, hhalting_n_c⟩ := hhalting_n
  have hencode : Computable (Encodable.encode : Nat.Partrec.Code → ℕ) := Primrec.encode.to_comp
  -- ofNatCode (encode c) = c  (decode ∘ encode = id for Code)
  have hdec_enc : ∀ c : Nat.Partrec.Code, ofNatCode (Encodable.encode c) = c := fun c =>
    Option.some_injective _ (by
      have h := @Encodable.encodek Nat.Partrec.Code _ c
      simp only [Encodable.decode] at h; exact h)
  -- Build DecidablePred on Code by transporting hdec_n through the bijection
  have hdec_code : DecidablePred (fun c : Nat.Partrec.Code => (c.eval 0).Dom) := fun c =>
    cast (by simp [hdec_enc c]) (hdec_n (Encodable.encode c))
  -- Conclude: halting problem on Code is decidable — contradiction
  exact ComputablePred.halting_problem 0
    ⟨hdec_code, (hhalting_n_c.comp hencode).of_eq fun c => by simp [hdec_enc c]⟩

end PeriodicTM
