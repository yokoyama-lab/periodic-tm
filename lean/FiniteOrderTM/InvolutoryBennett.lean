/-
FiniteOrderTM/InvolutoryBennett.lean

Roadmap step 3 (Bennett/Lecerf reversibilisation) — the fully verified core.

The paper-level construction is compute–copy–uncompute: run a machine `F`
forward on the work banks, copy its output onto a fresh ancilla bank, then
run the *flip* of `F` to restore the work banks.  This file assembles that
composite from the repo's verified combinators only:

* `bennettWith F σ qf C c₀` — the generic F;C;U composite
  `seq (seq (liftL F) C c₀) (liftL (flipM F σ)) (σ qf)` on the doubled bank
  index `ι ⊕ ι` (left = work, right = ancilla), with an arbitrary copy leg
  `C`; `bennett F σ qf` instantiates `C := copyM` (the single-cell copy).

* **Main theorem** `bennett_ktapeSem`: for a syntactically reversible `F`
  (the weakest hypothesis under which the repo can *construct* the
  uncompute leg, via `flipM`), the composite computes, as an *equation of
  partial functions with no domain restriction on the ancilla content*,

      ⟦bennett F⟧ (X, A)  =  ⟦F⟧ X  ▷ fun Y => (X, A ⟵heads Y)

  i.e. `x ↦ (x, f x)`-style semantics on separate banks: the work bank is
  restored to `X` exactly, and each ancilla head receives the corresponding
  output head of `f x`.  The forward inclusion is pure Kleisli plumbing
  (`ktapeSem_seq`, `ktapeSem_liftL`, `flipM_tapeSem_inverse`); the converse
  inclusion additionally consumes injectivity of `⟦F⟧`
  (`KReversible.semInverse` + `SemInverse.injective`), because the
  uncompute leg could a priori halt at any preimage of `Y`.

* `bennettWith_mem` — the membership-level compute–copy–uncompute lemma for
  an *arbitrary* copy leg `C` that preserves the work banks; instantiated by
  `bennett_copyStr_mem` with the full-string traversal copy `copyStr`, giving
  the string-level (whole output block, not just heads) Bennett composite on
  its blank-ancilla / block-shaped-output domain.

* `writeK` — a small but genuine class of syntactically reversible machines
  (head-vector involutions), with `KReversible`/halt/entry discharged, and a
  sanity `example` computing `bennett (writeK g)` in closed form.

* `Reversibilisation` / `ReversibilisationGoal` — the reversibilisation
  interface the transport file (`InvolutoryTransport.lean`) still needs:
  a syntactic reversibiliser `K` (Unit-bank, `KReversible` + halt/entry
  discipline + involutive state map) with the same `stringSem` as a given
  `R`.  Proved for the class of machines that are already syntactically
  reversible (`Reversibilisation.ofK_self`, `reversibilisation_toK`); the
  general Bennett-history form is stated as the `Prop`
  `ReversibilisationGoal`.  `conjugationClosure_of_reversibilisation` then
  closes the loop: any `R` with a `Reversibilisation` witness admits the
  machine-level conjugation closure of `InvolutoryTransport.lean`.
-/
import FiniteOrderTM.InvolutoryTransport
import FiniteOrderTM.Copy

namespace PeriodicTM

open Turing Turing.TM0

variable {Γ : Type*} [Inhabited Γ] {Λ : Type*} {ι : Type*}

/-! ### Closed-form semantics of the single-write machines -/

/-- Closed form of the single-cell copy's semantics: one write, total. -/
theorem ktapeSem_copyM (T : ι ⊕ ι → Tape Γ) :
    ktapeSem (copyM (Γ := Γ) (ι := ι)) false T
      = Part.some ((KStmt.write (fun i => match i with
          | Sum.inl s => headsV T (Sum.inl s)
          | Sum.inr t => headsV T (Sum.inl t))).apply T) := by
  ext V
  rw [singleWrite_ktapeSem copyM (fun b i => match i with
    | Sum.inl s => b (Sum.inl s) | Sum.inr t => b (Sum.inl t))
    (fun _ => rfl) (fun _ => rfl)]
  exact Part.mem_some_iff.symm

/-- On a split bank `(work = Y, ancilla = A)`, the single-cell copy leaves
the work banks untouched and overwrites each ancilla head with the
corresponding work head. -/
theorem ktapeSem_copyM_withR (A Y : ι → Tape Γ) :
    ktapeSem (copyM (Γ := Γ) (ι := ι)) false (withR A Y)
      = Part.some (withR (fun t => (A t).write ((Y t).1)) Y) := by
  rw [ktapeSem_copyM]
  congr 1
  funext j
  rcases j with s | t
  · exact Tape.write_self (Y s)
  · rfl

/-! ### The Bennett composite -/

/-- The generic Bennett compute–copy–uncompute composite on the doubled bank
index `ι ⊕ ι` (left = work, right = ancilla): run `F` on the work banks,
run the copy leg `C` on the full bank, then run the flip of `F` on the work
banks to restore the input.  Noncomputable because `flipM` is. -/
noncomputable def bennettWith (F : KMachine Γ Λ ι) (σ : Λ → Λ) (qf : Λ)
    {ΛC : Type*} (C : KMachine Γ ΛC (ι ⊕ ι)) (c₀ : ΛC) :
    KMachine Γ ((Λ ⊕ ΛC) ⊕ Λ) (ι ⊕ ι) :=
  seq (seq (liftL F (κ := ι)) C c₀) (liftL (flipM F σ) (κ := ι)) (σ qf)

/-- The Bennett composite with the single-cell copy leg. -/
noncomputable def bennett (F : KMachine Γ Λ ι) (σ : Λ → Λ) (qf : Λ) :
    KMachine Γ ((Λ ⊕ Bool) ⊕ Λ) (ι ⊕ ι) :=
  bennettWith F σ qf copyM false

/-- Unconditional Kleisli decomposition of the composite (no hypotheses at
all — `seq` needs none). -/
theorem bennettWith_ktapeSem_bind (F : KMachine Γ Λ ι) (σ : Λ → Λ)
    (qf : Λ) {ΛC : Type*} (C : KMachine Γ ΛC (ι ⊕ ι)) (c₀ : ΛC)
    (q0 : Λ) (T : ι ⊕ ι → Tape Γ) :
    ktapeSem (bennettWith F σ qf C c₀) (Sum.inl (Sum.inl q0)) T
      = ((ktapeSem (liftL F (κ := ι)) q0 T).bind (ktapeSem C c₀)).bind
          (ktapeSem (liftL (flipM F σ) (κ := ι)) (σ qf)) := by
  rw [bennettWith, ktapeSem_seq, ktapeSem_seq]

/-- **Membership-level compute–copy–uncompute**, generic in the copy leg:
if `Y ∈ ⟦F⟧ X`, the copy leg maps `(Y, A)` to `W` while preserving the work
banks (`W ∘ inl = Y`), then the Bennett composite maps `(X, A)` to
`(X, W ∘ inr)` — output captured on the ancilla, input restored.  Consumes
exactly the syntactic-reversibility package that `flipM` needs. -/
theorem bennettWith_mem {F : KMachine Γ Λ ι} {σ : Λ → Λ} {q0 qf : Λ}
    (hσ : ∀ q, σ (σ q) = q) (hrev : KReversible F)
    (hhalt : ∀ q a, F q a = none ↔ q = qf)
    (hent : ∀ q b, (∃ v, Demand F q b v) ↔ q ≠ q0)
    {ΛC : Type*} {C : KMachine Γ ΛC (ι ⊕ ι)} {c₀ : ΛC}
    {X Y : ι → Tape Γ} {A : ι → Tape Γ} {W : ι ⊕ ι → Tape Γ}
    (hY : Y ∈ ktapeSem F q0 X)
    (hW : W ∈ ktapeSem C c₀ (withR A Y))
    (hWork : W ∘ Sum.inl = Y) :
    withR (W ∘ Sum.inr) X
      ∈ ktapeSem (bennettWith F σ qf C c₀) (Sum.inl (Sum.inl q0))
          (withR A X) := by
  rw [bennettWith_ktapeSem_bind, Part.mem_bind_iff]
  refine ⟨W, Part.mem_bind_iff.mpr ⟨withR A Y, ?_, hW⟩, ?_⟩
  · rw [ktapeSem_liftL]
    exact (Part.mem_map_iff _).mpr ⟨Y, hY, rfl⟩
  · have hWsplit : W = withR (W ∘ Sum.inr) Y := by
      rw [← hWork]; exact (Sum.elim_comp_inl_inr W).symm
    rw [hWsplit, ktapeSem_liftL]
    exact (Part.mem_map_iff _).mpr
      ⟨X, (flipM_tapeSem_inverse hσ hrev hhalt hent).mp hY, rfl⟩

/-- **Main theorem (roadmap step 3, head-valued case): the Bennett composite
computes `x ↦ (x, f x)` on separate tape banks, as an equality of partial
functions.**  For syntactically reversible `F` with the halt/entry
discipline, on any split input `(work = X, ancilla = A)`:

    ⟦bennett F⟧ (X, A) = ⟦F⟧ X  ▷ fun Y => (X, fun t => (A t) with head := (Y t).head).

The work bank returns to `X` exactly; each ancilla tape receives the head
of the corresponding output tape of `F`.  The `⊇` inclusion is combinator
plumbing; the `⊆` inclusion uses injectivity of `⟦F⟧` (via
`KReversible.semInverse`) to pin the uncompute leg's output to `X`. -/
theorem bennett_ktapeSem {F : KMachine Γ Λ ι} {σ : Λ → Λ} {q0 qf : Λ}
    (hσ : ∀ q, σ (σ q) = q) (hrev : KReversible F)
    (hhalt : ∀ q a, F q a = none ↔ q = qf)
    (hent : ∀ q b, (∃ v, Demand F q b v) ↔ q ≠ q0)
    (X A : ι → Tape Γ) :
    ktapeSem (bennett F σ qf) (Sum.inl (Sum.inl q0)) (withR A X)
      = (ktapeSem F q0 X).map
          (fun Y => withR (fun t => (A t).write ((Y t).1)) X) := by
  rw [bennett, bennettWith_ktapeSem_bind, ktapeSem_liftL]
  ext V
  constructor
  · intro hV
    rw [Part.mem_bind_iff] at hV
    obtain ⟨W, hW, hV⟩ := hV
    rw [Part.mem_bind_iff] at hW
    obtain ⟨U, hU, hW⟩ := hW
    obtain ⟨Y, hY, rfl⟩ := (Part.mem_map_iff _).mp hU
    rw [ktapeSem_copyM_withR, Part.mem_some_iff] at hW
    subst hW
    rw [ktapeSem_liftL] at hV
    obtain ⟨X', hX', rfl⟩ := (Part.mem_map_iff _).mp hV
    have hYX' : Y ∈ ktapeSem F q0 X' :=
      (flipM_tapeSem_inverse hσ hrev hhalt hent).mpr hX'
    have hXX' : X = X' :=
      (KReversible.semInverse hσ hrev hhalt hent).injective
        trivial trivial hY hYX'
    exact (Part.mem_map_iff _).mpr ⟨Y, hY, by rw [hXX']⟩
  · intro hV
    obtain ⟨Y, hY, rfl⟩ := (Part.mem_map_iff _).mp hV
    rw [Part.mem_bind_iff]
    refine ⟨withR (fun t => (A t).write ((Y t).1)) Y,
      Part.mem_bind_iff.mpr ⟨withR A Y, (Part.mem_map_iff _).mpr ⟨Y, hY, rfl⟩,
        by rw [ktapeSem_copyM_withR]; exact Part.mem_some_iff.mpr rfl⟩, ?_⟩
    rw [ktapeSem_liftL]
    exact (Part.mem_map_iff _).mpr
      ⟨X, (flipM_tapeSem_inverse hσ hrev hhalt hent).mp hY, rfl⟩

/-- Membership form of the main theorem. -/
theorem bennett_mem_iff {F : KMachine Γ Λ ι} {σ : Λ → Λ} {q0 qf : Λ}
    (hσ : ∀ q, σ (σ q) = q) (hrev : KReversible F)
    (hhalt : ∀ q a, F q a = none ↔ q = qf)
    (hent : ∀ q b, (∃ v, Demand F q b v) ↔ q ≠ q0)
    (X A : ι → Tape Γ) (V : ι ⊕ ι → Tape Γ) :
    V ∈ ktapeSem (bennett F σ qf) (Sum.inl (Sum.inl q0)) (withR A X)
      ↔ ∃ Y ∈ ktapeSem F q0 X,
          V = withR (fun t => (A t).write ((Y t).1)) X := by
  rw [bennett_ktapeSem hσ hrev hhalt hent, Part.mem_map_iff]
  constructor
  · rintro ⟨Y, hY, rfl⟩; exact ⟨Y, hY, rfl⟩
  · rintro ⟨Y, hY, rfl⟩; exact ⟨Y, hY, rfl⟩

/-- The Bennett composite restores the work banks exactly. -/
theorem bennett_work_restored {F : KMachine Γ Λ ι} {σ : Λ → Λ} {q0 qf : Λ}
    (hσ : ∀ q, σ (σ q) = q) (hrev : KReversible F)
    (hhalt : ∀ q a, F q a = none ↔ q = qf)
    (hent : ∀ q b, (∃ v, Demand F q b v) ↔ q ≠ q0)
    {X A : ι → Tape Γ} {V : ι ⊕ ι → Tape Γ}
    (hV : V ∈ ktapeSem (bennett F σ qf) (Sum.inl (Sum.inl q0)) (withR A X)) :
    V ∘ Sum.inl = X := by
  obtain ⟨Y, -, rfl⟩ := (bennett_mem_iff hσ hrev hhalt hent X A V).mp hV
  rfl

/-- The Bennett composite halts exactly where `F` halts (same domain). -/
theorem bennett_dom_iff {F : KMachine Γ Λ ι} {σ : Λ → Λ} {q0 qf : Λ}
    (hσ : ∀ q, σ (σ q) = q) (hrev : KReversible F)
    (hhalt : ∀ q a, F q a = none ↔ q = qf)
    (hent : ∀ q b, (∃ v, Demand F q b v) ↔ q ≠ q0)
    (X A : ι → Tape Γ) :
    (ktapeSem (bennett F σ qf) (Sum.inl (Sum.inl q0)) (withR A X)).Dom
      ↔ (ktapeSem F q0 X).Dom := by
  rw [bennett_ktapeSem hσ hrev hhalt hent]
  exact Iff.rfl

/-! ### The string-level instance: `copyStr` as the copy leg

`bennettWith` with the full-string traversal copy `copyStr` (on `ι = Unit`)
captures the *entire* output block on the ancilla, not just the head.  The
copy leg is domain-gated (blank ancilla, block-shaped work output), so the
result is a membership statement on that domain. -/

section BennettStr
variable [DecidableEq Γ]

/-- **String-level compute–copy–uncompute** (membership form).  If
`Y ∈ ⟦F⟧ X`, the ancilla `A` is blank, and the work output `Y` is a
blank-free block of length `n` anchored at home, then the Bennett composite
with copy leg `copyStr` maps `(X, A)` to `(X, Z)` where `Z` carries exactly
the length-`n` output block of `Y` (blank elsewhere). -/
theorem bennett_copyStr_mem {F : KMachine Γ Λ Unit} {σ : Λ → Λ} {q0 qf : Λ}
    (hσ : ∀ q, σ (σ q) = q) (hrev : KReversible F)
    (hhalt : ∀ q a, F q a = none ↔ q = qf)
    (hent : ∀ q b, (∃ v, Demand F q b v) ↔ q ≠ q0)
    {X Y A : Unit → Tape Γ} (hY : Y ∈ ktapeSem F q0 X)
    (hblank : ∀ m : ℤ, (A ()).nth m = default)
    (hanchor : (Y ()).nth (-1) = default)
    (n : ℕ) (hblock : ∀ i : ℕ, i < n → (Y ()).nth i ≠ default)
    (hend : (Y ()).nth n = default) :
    ∃ W : Unit ⊕ Unit → Tape Γ,
      withR (W ∘ Sum.inr) X
        ∈ ktapeSem (bennettWith F σ qf copyStr CopyState.copy)
            (Sum.inl (Sum.inl q0)) (withR A X) ∧
      ∀ m : ℤ, (W (Sum.inr ())).nth m
        = if 0 ≤ m ∧ m < (n : ℤ) then (Y ()).nth m else default := by
  -- the copy leg's input is `(work = Y, ancilla = A)`; its domain conditions
  -- are exactly the block/blank hypotheses.
  have hDom : CopyDomIn (withR A Y) :=
    ⟨hanchor, hblank, n, hblock, hend⟩
  have hW : retTape n ((KStmt.move (fun _ => some Dir.left)).apply
        (sweepTape n (withR A Y)))
      ∈ ktapeSem copyStr CopyState.copy (withR A Y) :=
    copyStr_output_mem n (withR A Y) hblock hend hanchor
  refine ⟨_, bennettWith_mem hσ hrev hhalt hent hY hW ?_, ?_⟩
  · funext u
    cases u
    exact copyStr_preserves_src (withR A Y) _ hDom hW
  · intro m
    rw [copyStr_run_tgt_nth n (withR A Y) m]
    by_cases hm : (0 : ℤ) ≤ m ∧ m < (n : ℤ)
    · rw [if_pos hm, if_pos hm]; rfl
    · rw [if_neg hm, if_neg hm]
      exact hblank m

end BennettStr

/-! ### A verified class of reversible machines: head-vector involutions -/

/-- The one-shot writer applying `g` to the whole head vector. -/
def writeK (g : (ι → Γ) → (ι → Γ)) : KMachine Γ Bool ι := fun q b =>
  match q with
  | false => some (true, KStmt.write (g b))
  | true => none

omit [Inhabited Γ] in
theorem writeK_halt_iff (g : (ι → Γ) → (ι → Γ)) :
    ∀ q a, writeK (Γ := Γ) g q a = none ↔ q = true := by
  intro q a; cases q <;> simp [writeK]

omit [Inhabited Γ] in
/-- The demands of `writeK g`: only at the halt state, only write-backs of
`g`-preimages. -/
theorem writeK_demand {g : (ι → Γ) → (ι → Γ)} {q : Bool} {b : ι → Γ}
    {v : Bool × KStmt Γ ι} :
    Demand (writeK (Γ := Γ) g) q b v
      ↔ q = true ∧ ∃ a, g a = b ∧ v = (false, KStmt.write a) := by
  constructor
  · intro h
    cases h with
    | @write p a _ _ h₀ =>
      cases p
      · have h₁ : ((true, KStmt.write (g a)) : Bool × KStmt Γ ι)
            = (q, KStmt.write b) := Option.some.inj h₀
        obtain ⟨hq, hb⟩ := Prod.mk.injEq .. ▸ h₁
        exact ⟨hq.symm, a, KStmt.write.inj hb, rfl⟩
      · simp [writeK] at h₀
    | @move p a _ _ _ h₀ => cases p <;> simp [writeK] at h₀
    | @perm p a _ _ _ h₀ => cases p <;> simp [writeK] at h₀
  · rintro ⟨rfl, a, rfl, rfl⟩
    exact Demand.write rfl

omit [Inhabited Γ] in
/-- `writeK g` is syntactically reversible for involutive `g`. -/
theorem writeK_reversible {g : (ι → Γ) → (ι → Γ)}
    (hg : ∀ x, g (g x) = x) : KReversible (writeK (Γ := Γ) g) where
  backdet := by
    intro q b v₁ v₂ h₁ h₂
    obtain ⟨-, a₁, hb₁, rfl⟩ := writeK_demand.mp h₁
    obtain ⟨-, a₂, hb₂, rfl⟩ := writeK_demand.mp h₂
    have ha : a₁ = a₂ := by
      have h := hb₁.trans hb₂.symm
      calc a₁ = g (g a₁) := (hg a₁).symm
        _ = g (g a₂) := by rw [h]
        _ = a₂ := hg a₂
    rw [ha]
  move_uniform := by
    intro p a q d h; cases p <;> simp [writeK] at h
  perm_uniform := by
    intro p a q π h; cases p <;> simp [writeK] at h

omit [Inhabited Γ] in
/-- `writeK g` satisfies the entry discipline for involutive `g`. -/
theorem writeK_entry {g : (ι → Γ) → (ι → Γ)} (hg : ∀ x, g (g x) = x) :
    ∀ (q : Bool) (b : ι → Γ),
      (∃ v, Demand (writeK (Γ := Γ) g) q b v) ↔ q ≠ false := by
  intro q b
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨rfl, -⟩ := writeK_demand.mp hv
    simp
  · intro hq
    have hq' : q = true := by
      cases q
      · exact absurd rfl hq
      · rfl
    subst hq'
    exact ⟨(false, KStmt.write (g b)),
      writeK_demand.mpr ⟨rfl, g b, hg b, rfl⟩⟩

/-- Closed-form semantics of `writeK`. -/
theorem ktapeSem_writeK (g : (ι → Γ) → (ι → Γ)) (X : ι → Tape Γ) :
    ktapeSem (writeK (Γ := Γ) g) false X
      = Part.some ((KStmt.write (g (headsV X))).apply X) := by
  ext V
  rw [singleWrite_ktapeSem (writeK g) g (fun _ => rfl) (fun _ => rfl)]
  exact Part.mem_some_iff.symm

/-- **Sanity example.**  The Bennett composite of the head-vector involution
`writeK g` computes, totally and in closed form, exactly
`(X, A) ↦ (X, A ⟵heads g(heads X))`: work restored, `g` of the input heads
captured on the ancilla. -/
example {g : (ι → Γ) → (ι → Γ)} (hg : ∀ x, g (g x) = x)
    (X A : ι → Tape Γ) :
    ktapeSem (bennett (writeK (Γ := Γ) g) not true)
        (Sum.inl (Sum.inl false)) (withR A X)
      = Part.some (withR (fun t => (A t).write (g (headsV X) t)) X) := by
  rw [bennett_ktapeSem Bool.not_not (writeK_reversible hg)
      (writeK_halt_iff g) (writeK_entry hg), ktapeSem_writeK, Part.map_some]
  rfl

/-- Degenerate sanity check: with `g = id` the composite duplicates the
input heads onto the ancilla. -/
example (X A : ι → Tape Γ) :
    ktapeSem (bennett (writeK (Γ := Γ) (id : (ι → Γ) → (ι → Γ))) not true)
        (Sum.inl (Sum.inl false)) (withR A X)
      = Part.some (withR (fun t => (A t).write (headsV X t)) X) := by
  rw [bennett_ktapeSem Bool.not_not (writeK_reversible fun _ => rfl)
      (writeK_halt_iff id) (writeK_entry fun _ => rfl),
    ktapeSem_writeK, Part.map_some]
  rfl

/-! ### The reversibilisation interface for the transport file -/

/-- `K` is a **syntactic reversibilisation** of the string function of `R`:
a `Unit`-bank machine carrying the full syntactic-reversibility package
(`KReversible`, halt/entry discipline, involutive state map) whose collapsed
`TM0` machine has the same string semantics as `R`.  A witness of this
structure is exactly what `conj_syntacticallyInvolutory_ofK` /
`conjugationClosure_tapeSem` (InvolutoryTransport.lean) demand of their
conjugator. -/
structure Reversibilisation {Λ : Type*} [Inhabited Λ]
    (R : Machine Γ Λ) (r₀ : Λ)
    {ΛK : Type*} [Inhabited ΛK]
    (K : KMachine Γ ΛK Unit) (σK : ΛK → ΛK) (k₀ kf : ΛK) : Prop where
  invol : ∀ q, σK (σK q) = q
  rev : KReversible K
  halt_iff : ∀ q a, K q a = none ↔ q = kf
  entry : ∀ q b, (∃ v, Demand K q b v) ↔ q ≠ k₀
  sem : ∀ s, stringSem (ofK K) k₀ s = stringSem R r₀ s

/-- Every `Unit`-bank machine with the syntactic package reversibilises its
own collapse — the (nontrivial-in-content, trivial-in-proof) base class. -/
theorem Reversibilisation.ofK_self {ΛK : Type*} [Inhabited ΛK]
    {K : KMachine Γ ΛK Unit} {σK : ΛK → ΛK} {k₀ kf : ΛK}
    (h1 : ∀ q, σK (σK q) = q) (h2 : KReversible K)
    (h3 : ∀ q a, K q a = none ↔ q = kf)
    (h4 : ∀ q b, (∃ v, Demand K q b v) ↔ q ≠ k₀) :
    Reversibilisation (ofK K) k₀ K σK k₀ kf :=
  ⟨h1, h2, h3, h4, fun _ => rfl⟩

/-- A `TM0` machine that is already syntactically reversible (as witnessed
on its embedding `toK R`) is its own reversibilisation. -/
theorem reversibilisation_toK {Λ : Type*} [Inhabited Λ]
    {R : Machine Γ Λ} {σ : Λ → Λ} {r₀ rf : Λ}
    (h1 : ∀ q, σ (σ q) = q) (h2 : KReversible (toK R))
    (h3 : ∀ q a, toK R q a = none ↔ q = rf)
    (h4 : ∀ q b, (∃ v, Demand (toK R) q b v) ↔ q ≠ r₀) :
    Reversibilisation R r₀ (toK R) σ r₀ rf :=
  ⟨h1, h2, h3, h4, fun s => by rw [ofK_toK]⟩

/-- **The general reversibilisation goal** (Bennett/Lecerf, stated as a
`Prop`): every semantically invertible string function computed by a `TM0`
machine admits a syntactic reversibilisation.  This is the exact missing
hypothesis-shape separating `conjugationClosure_tapeSem` from
`StringConjugationClosure` (see the roadmap delta of
`InvolutoryTransport.lean`, item (i)). -/
def ReversibilisationGoal : Prop :=
  ∀ (Γ ΛR : Type) [Inhabited Γ] [Inhabited ΛR]
    (R R' : Machine Γ ΛR) (r₀ r₀' : ΛR),
    (∀ s t, t ∈ stringSem R r₀ s ↔ s ∈ stringSem R' r₀' t) →
    ∃ (ΛK : Type) (_ : Inhabited ΛK) (K : KMachine Γ ΛK Unit)
      (σK : ΛK → ΛK) (k₀ kf : ΛK),
      Reversibilisation R r₀ K σK k₀ kf

/-- **Conjugation closure for reversibilisable conjugators**: any `R` with a
`Reversibilisation` witness `K` yields a syntactically involutory `TM0`
machine computing the conjugation of `⟦M⟧` by `⟦ofK K⟧` (whose `stringSem`
is that of `R`), with post-machine `flipM K σK`.  This composes
`conjugationClosure_tapeSem` with the reversibilisation interface — the
machine-level shape that `StringConjugationClosure` needs, still at
`tapeSem` level (the remaining gap is the `StdOutput`/standard-intermediate
argument, see roadmap delta below). -/
theorem conjugationClosure_of_reversibilisation
    (Γ ΛR ΛK ΛM : Type) [Inhabited Γ] [Inhabited ΛR] [Inhabited ΛK]
    [Inhabited ΛM]
    (R : Machine Γ ΛR) (r₀ : ΛR)
    (K : KMachine Γ ΛK Unit) (σK : ΛK → ΛK) (k₀ kf : ΛK)
    (M : Machine Γ ΛM) (σM : ΛM → ΛM) (q0M qfM : ΛM)
    (hK : Reversibilisation R r₀ K σK k₀ kf)
    (hM : Involutory M σM q0M qfM) :
    (∀ s, stringSem (ofK K) k₀ s = stringSem R r₀ s) ∧
    ∃ (Λ' : Type) (_ : Inhabited Λ') (D : Machine Γ Λ') (d₀ df : Λ'),
      SyntacticallyInvolutory D d₀ df ∧
      ∀ T, tapeSem D d₀ T
        = (tapeSem (ofK K) k₀ T).bind fun u =>
            (tapeSem M q0M u).bind fun v =>
              (ktapeSem (flipM K σK) (σK kf) (fun _ => v)).map fun U =>
                U () := by
  refine ⟨hK.sem, ?_⟩
  obtain ⟨Λ', inst, D, d₀, df, hsyn, hsem⟩ :=
    conjugationClosure_tapeSem Γ ΛK ΛM K M σK σM k₀ kf q0M qfM hM
      hK.invol hK.rev hK.halt_iff hK.entry
  refine ⟨Λ', inst, D, d₀, df, hsyn, fun T => ?_⟩
  rw [tapeSem_ofK]
  exact hsem T

/-!
### Roadmap delta (step 3: Bennett/Lecerf reversibilisation)

**Done here (all fully verified, no admitted proofs):**
* The Bennett compute–copy–uncompute composite as an object
  (`bennettWith` / `bennett`), assembled purely from the repo's verified
  combinators (`seq`, `liftL`, `flipM`, `copyM`/`copyStr`), with the
  unconditional Kleisli decomposition `bennettWith_ktapeSem_bind`.
* **The full `x ↦ (x, f x)` semantics equation** `bennett_ktapeSem` for
  syntactically reversible `F` — not just the compute–copy stage: the
  uncompute leg is included and verified, with the work banks provably
  restored (`bennett_work_restored`) and the domain preserved
  (`bennett_dom_iff`).  Head-valued output capture (single-cell copy).
* The generic membership lemma `bennettWith_mem` for any work-preserving
  copy leg, instantiated at string level by `bennett_copyStr_mem`: the
  whole length-`n` output block of `⟦F⟧` captured on a blank ancilla, on
  the traversal copy's block domain.
* A verified nontrivial machine class (`writeK`, head-vector involutions)
  discharging `KReversible` + halt/entry, with closed-form sanity
  `example`s for `bennett (writeK g)`.
* The reversibilisation interface (`Reversibilisation`), its trivially
  reachable instances (`ofK_self`, `reversibilisation_toK` — the class of
  already-syntactically-reversible conjugators), the general Bennett
  history form as the `Prop` `ReversibilisationGoal`, and
  `conjugationClosure_of_reversibilisation` plugging any witness straight
  into the machine-level conjugation closure of `InvolutoryTransport.lean`.

**Honest accounting — what `bennett_ktapeSem` does *not* yet give:**
* Its hypothesis is `KReversible F`.  The Bennett construction's *point*
  is to apply it to a **non**-reversible `F` by first simulating `F` with
  a history-logging descriptor machine (the removed WIP `phaseF2` attempt;
  see `git log -- 'lean/FiniteOrderTM/Bennett*'`).  That history simulator
  — a fresh machine construction with a `reachesN`-style traversal proof,
  not a combinator composite — is the sole missing ingredient of
  `ReversibilisationGoal`; once it exists with a `SemInverse` witness,
  `conj_partial_involution_sem` (SemReversible.lean) already consumes it
  at function level, and `bennettWith_mem` at machine level.
* `bennett` lives on banks `ι ⊕ ι`; the composite is *not* claimed
  syntactically involutory or reversible itself (its copy leg is not), so
  it feeds the `SemInverse`-based route (`conj_partial_involution_sem`),
  not `conj_KInvolutory`.

**Remaining for step 4 (assembly of `StringConjugationClosure` /
`StringCompletenessGoal`):**
1. Discharge `ReversibilisationGoal` for a class beyond
   already-reversible machines: history-logging simulation of an arbitrary
   `TM0` step relation (Bennett's F-phase) + its `SemInverse` witness,
   then erase the input copy using the semantic inverse `R'` (this is
   where the hypothesis `⟦R⟧⁻¹ = ⟦R'⟧` of `StringConjugationClosure` is
   consumed).
2. `StdOutput` for the collapsed conjugate of
   `conjugationClosure_of_reversibilisation`, plus standardness of the
   intermediate tapes, to turn its `tapeSem` equation into the `stringSem`
   equation of `StringConjugationClosure` (read `s.length` symbols via
   `readTape_mk₁`).
3. Multi-bank encoding (`Lift`/`Reindex` + hidden-bank encoding) to state
   the 2k-tape completeness form `StringCompletenessGoal`.
-/

end PeriodicTM
