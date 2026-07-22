/-
FiniteOrderTM/CopyMulti.lean

Multi-tape full-string copy.  The single-pair traversal copy `copyStr`
(`Unit ⊕ Unit`) is transported to copy an arbitrary *designated* bank pair
`s → t` of a larger index `ι'`, freezing every other bank.  This is the building
block for the multi-tape Bennett wrapper: copying work tape `j` onto ancilla tape
`j` is `copyStrAt (work j) (ancilla j)`.

The transport is `renameBank (selEquiv s t) (liftL copyStr)`, where `selEquiv`
splits `ι'` into the two active banks `{s, t}` (carrying `copyStr`'s source/target)
and the frozen complement `{x // x ≠ s ∧ x ≠ t}`.  Reuses `copyStr_semInverse` and
`SemInverse.liftL` / `SemInverse.renameBank` unchanged.
-/
import FiniteOrderTM.Copy

namespace PeriodicTM

open Turing CopyState

variable {Γ : Type*} [Inhabited Γ] [DecidableEq Γ] {ι' : Type*} [DecidableEq ι']

/-- The two active banks (source `s`, target `t`) of a designated-pair copy. -/
def activeP (s t : ι') : ι' → Prop := fun b => b = s ∨ b = t

instance (s t : ι') : DecidablePred (activeP s t) := fun b => by
  unfold activeP; infer_instance

/-- `Unit ⊕ Unit` (copyStr's source/target) names the two active banks `{s, t}`. -/
def twoEquiv (s t : ι') (hst : s ≠ t) : (Unit ⊕ Unit) ≃ {x // activeP s t x} where
  toFun := fun
    | Sum.inl () => ⟨s, Or.inl rfl⟩
    | Sum.inr () => ⟨t, Or.inr rfl⟩
  invFun := fun ⟨x, _⟩ => if x = s then Sum.inl () else Sum.inr ()
  left_inv := by rintro (⟨⟩ | ⟨⟩) <;> simp [hst, Ne.symm hst]
  right_inv := by rintro ⟨x, (rfl | rfl)⟩ <;> simp [hst, Ne.symm hst]

/-- Split `ι'` into the active pair `{s, t}` (named by `Unit ⊕ Unit`) and the
frozen complement. -/
noncomputable def selEquiv (s t : ι') (hst : s ≠ t) :
    ((Unit ⊕ Unit) ⊕ {x // ¬ activeP s t x}) ≃ ι' :=
  (Equiv.sumCongr (twoEquiv s t hst) (Equiv.refl _)).trans (Equiv.sumCompl (activeP s t))

/-- **Designated-pair full-string copy**: copy bank `s` onto bank `t` of `ι'`,
freezing all other banks. -/
noncomputable def copyStrAt (s t : ι') (hst : s ≠ t) : KMachine Γ CopyState ι' :=
  renameBank (selEquiv s t hst) (liftL (copyStr (Γ := Γ)) (κ := {x // ¬ activeP s t x}))

/-- The reverse designated-pair copy (blanks the target). -/
noncomputable def copyStrAtRev (s t : ι') (hst : s ≠ t) : KMachine Γ CopyState ι' :=
  renameBank (selEquiv s t hst) (liftL (copyStrRev (Γ := Γ)) (κ := {x // ¬ activeP s t x}))

/-- **The designated-pair copy is semantically reversible.**  `copyStr_semInverse`
transported through `liftL` (frozen complement) and `renameBank (selEquiv s t)`.
The input domain constrains only the two active banks: source `s` an anchored
blank-free block, target `t` blank. -/
theorem copyStrAt_semInverse (s t : ι') (hst : s ≠ t) :
    SemInverse (Γ := Γ) (copyStrAt s t hst) (copyStrAtRev s t hst)
      CopyState.copy CopyState.copy
      (fun T' => CopyDomIn (fun i => T' (selEquiv s t hst (Sum.inl i))))
      (fun T' => CopyDomOut (fun i => T' (selEquiv s t hst (Sum.inl i)))) :=
  (copyStr_semInverse.liftL (κ := {x // ¬ activeP s t x})).renameBank (selEquiv s t hst)

/-! #### `selEquiv` computation lemmas (for the preserves-others hand-over) -/

theorem selEquiv_inl_inl (s t : ι') (hst : s ≠ t) :
    selEquiv s t hst (Sum.inl (Sum.inl ())) = s := by
  simp only [selEquiv, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl,
    Equiv.sumCompl_apply_inl]; rfl

theorem selEquiv_inr (s t : ι') (hst : s ≠ t) (x : {b // ¬ activeP s t b}) :
    selEquiv s t hst (Sum.inr x) = (x : ι') := by
  simp only [selEquiv, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr,
    Equiv.refl_apply, Equiv.sumCompl_apply_inr]

theorem selEquiv_symm_s (s t : ι') (hst : s ≠ t) :
    (selEquiv s t hst).symm s = Sum.inl (Sum.inl ()) := by
  have hps : activeP s t s := Or.inl rfl
  simp only [selEquiv, Equiv.symm_trans_apply, Equiv.sumCompl_symm_apply_of_pos hps,
    Equiv.sumCongr_symm, Equiv.refl_symm, Equiv.sumCongr_apply, Sum.map_inl]
  congr 1
  show (if s = s then Sum.inl () else Sum.inr ()) = Sum.inl ()
  rw [if_pos rfl]

theorem selEquiv_symm_frozen (s t : ι') (hst : s ≠ t) (b : ι') (h : ¬ activeP s t b) :
    (selEquiv s t hst).symm b = Sum.inr ⟨b, h⟩ := by
  simp only [selEquiv, Equiv.symm_trans_apply, Equiv.sumCompl_symm_apply_of_neg h,
    Equiv.sumCongr_symm, Equiv.refl_symm, Equiv.sumCongr_apply, Sum.map_inr, Equiv.refl_apply]

/-- **The designated-pair copy changes only the target bank `t`.**  The source `s`
is preserved (`copyStr_preserves_src`, domain-gated) and every frozen bank is
preserved (`liftL`).  This is the per-tape non-interference lemma needed to
sequence one copy per tape in the multi-tape wrapper (copy of tape `j` leaves all
other tapes' work⊕ancilla banks untouched). -/
theorem copyStrAt_preserves_others (s t : ι') (hst : s ≠ t) (Y V : ι' → Tape Γ)
    (hX : CopyDomIn (fun i => Y (selEquiv s t hst (Sum.inl i))))
    (hV : V ∈ ktapeSem (copyStrAt s t hst) CopyState.copy Y) :
    ∀ b, b ≠ t → V b = Y b := by
  rw [copyStrAt, ktapeSem_renameBank, Part.mem_map_iff] at hV
  obtain ⟨UL, hUL, rfl⟩ := hV
  obtain ⟨hfroz, hleft⟩ := ktapeSem_liftL_mem copyStr CopyState.copy hUL
  intro b hbt
  show UL ((selEquiv s t hst).symm b) = Y b
  by_cases hbs : b = s
  · subst hbs
    rw [selEquiv_symm_s]
    have hp := copyStr_preserves_src _ _ hX hleft
    simp only [Function.comp_apply, selEquiv_inl_inl] at hp
    exact hp
  · have hnotactive : ¬ activeP s t b := by
      show ¬ (b = s ∨ b = t); rintro (h | h)
      exacts [hbs h, hbt h]
    rw [selEquiv_symm_frozen s t hst b hnotactive]
    have hf := congrFun hfroz ⟨b, hnotactive⟩
    simp only [Function.comp_apply, selEquiv_inr] at hf
    exact hf

theorem selEquiv_inl_inr (s t : ι') (hst : s ≠ t) :
    selEquiv s t hst (Sum.inl (Sum.inr ())) = t := by
  simp only [selEquiv, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl,
    Equiv.sumCompl_apply_inl]; rfl

/-! #### Clean per-pair / per-list copy domains -/

/-- Clean copy domain on a designated pair: source `s` is an anchored blank-free
block and target `t` is blank.  Equal to `copyStrAt`'s transported domain
(`copyDomAt_iff`), but stated directly on the banks `s`, `t`. -/
def CopyDomAt (s t : ι') (X : ι' → Tape Γ) : Prop :=
  (X s).nth (-1) = default ∧ (∀ m : ℤ, (X t).nth m = default) ∧
  ∃ n : ℕ, (∀ i : ℕ, i < n → (X s).nth (i : ℤ) ≠ default) ∧ (X s).nth (n : ℤ) = default

/-- `copyStrAt`'s transported input domain is exactly `CopyDomAt s t`. -/
theorem copyDomAt_iff (s t : ι') (hst : s ≠ t) (X : ι' → Tape Γ) :
    CopyDomIn (fun i => X (selEquiv s t hst (Sum.inl i))) ↔ CopyDomAt s t X := by
  simp only [CopyDomIn, CopyDomAt, selEquiv_inl_inl, selEquiv_inl_inr]

/-- `CopyDomAt s t` depends only on banks `s` and `t`. -/
theorem CopyDomAt_congr (s t : ι') {U X : ι' → Tape Γ} (hs : U s = X s) (ht : U t = X t) :
    CopyDomAt s t U ↔ CopyDomAt s t X := by
  simp only [CopyDomAt, hs, ht]

/-- Combined input domain for the per-tape copy fold: each listed pair has its
`CopyDomAt`, and each pair's target is disjoint from every later pair's banks (so
copying it does not disturb the later copies). -/
def PairsDomIn : List {p : ι' × ι' // p.1 ≠ p.2} → (ι' → Tape Γ) → Prop
  | [], _ => True
  | p :: rest, X => CopyDomAt p.1.1 p.1.2 X ∧ PairsDomIn rest X ∧
      ∀ q ∈ rest, p.1.2 ≠ q.1.1 ∧ p.1.2 ≠ q.1.2

/-- `PairsDomIn l` depends only on the banks named in `l`. -/
theorem PairsDomIn_congr : (l : List {p : ι' × ι' // p.1 ≠ p.2}) → {U X : ι' → Tape Γ} →
    (∀ q ∈ l, U q.1.1 = X q.1.1 ∧ U q.1.2 = X q.1.2) →
    (PairsDomIn l U ↔ PairsDomIn l X)
  | [], _, _, _ => Iff.rfl
  | p :: rest, U, X, h => by
    have hp := h p (by simp)
    have hrest : ∀ q ∈ rest, U q.1.1 = X q.1.1 ∧ U q.1.2 = X q.1.2 :=
      fun q hq => h q (by simp [hq])
    simp only [PairsDomIn]
    rw [CopyDomAt_congr p.1.1 p.1.2 hp.1 hp.2, PairsDomIn_congr rest hrest]

/-! #### Base case for the per-tape fold: the immediately-halting machine -/

/-- The machine that halts at once, leaving every tape unchanged.  Base case of the
per-tape copy fold (copying an empty list of tape pairs). -/
def haltMachine : KMachine Γ Unit ι' := fun _ _ => none

theorem ktapeSem_haltMachine (T : ι' → Tape Γ) :
    ktapeSem (haltMachine (Γ := Γ) (ι' := ι')) () T = Part.some T := by
  have hstep : kstep (haltMachine (Γ := Γ) (ι' := ι')) (⟨(), T⟩ : KCfg Γ Unit ι') = none := rfl
  have he : (⟨(), T⟩ : KCfg Γ Unit ι') ∈
      StateTransition.eval (kstep (haltMachine (Γ := Γ) (ι' := ι'))) ⟨(), T⟩ :=
    StateTransition.mem_eval.mpr ⟨Relation.ReflTransGen.refl, hstep⟩
  unfold ktapeSem
  rw [Part.eq_some_iff.mpr he]; rfl

/-- The halting machine is its own semantic inverse (the identity relation). -/
theorem haltMachine_semInverse (Dom : (ι' → Tape Γ) → Prop) :
    SemInverse (haltMachine (Γ := Γ) (ι' := ι')) (haltMachine (Γ := Γ) (ι' := ι'))
      () () Dom Dom where
  fwd := fun X Y _ hY => by
    rw [ktapeSem_haltMachine] at hY ⊢
    rw [Part.mem_some_iff.mp hY]; exact Part.mem_some X
  bwd := fun X Y _ hX => by
    rw [ktapeSem_haltMachine] at hX ⊢
    rw [Part.mem_some_iff.mp hX]; exact Part.mem_some Y

/-! #### The per-tape copy fold (option A: reuse `copyStrAt` via `SemInverse.seq`)

Copy a *list* of designated tape pairs `(s, t)` (each `s ≠ t`) in order, on a fixed
bank index `ι'`.  The forward fold nests as `seq (copyStrAt p) (copyPairs rest)`;
its reverse mirrors `SemInverse.seq`'s `seq R₂' R₁'` shape, nesting the other way as
`seq (copyPairsRev rest) (copyStrAtRev p)`.  Instantiated with
`List.ofFn (fun j : Fin k => (work j, ancilla j))` this is the multi-tape copy. -/

/-- State of the forward copy fold over a pair list. -/
def FoldState : List {p : ι' × ι' // p.1 ≠ p.2} → Type
  | [] => Unit
  | _ :: rest => CopyState ⊕ FoldState rest

/-- Start state of the forward fold. -/
def foldStart : (l : List {p : ι' × ι' // p.1 ≠ p.2}) → FoldState l
  | [] => ()
  | _ :: _ => Sum.inl CopyState.copy

/-- Forward per-tape copy: copy each listed pair `s → t` in list order. -/
noncomputable def copyPairs : (l : List {p : ι' × ι' // p.1 ≠ p.2}) → KMachine Γ (FoldState l) ι'
  | [] => haltMachine
  | p :: rest => seq (copyStrAt p.1.1 p.1.2 p.2) (copyPairs rest) (foldStart rest)

/-- State of the reverse copy fold (mirrors `SemInverse.seq`'s `seq R₂' R₁'`). -/
def FoldStateRev : List {p : ι' × ι' // p.1 ≠ p.2} → Type
  | [] => Unit
  | _ :: rest => FoldStateRev rest ⊕ CopyState

/-- Start state of the reverse fold. -/
def foldStartRev : (l : List {p : ι' × ι' // p.1 ≠ p.2}) → FoldStateRev l
  | [] => ()
  | _ :: rest => Sum.inl (foldStartRev rest)

/-- Reverse per-tape copy: the inverse composition `copyPairsRev rest ; copyStrAtRev p`. -/
noncomputable def copyPairsRev : (l : List {p : ι' × ι' // p.1 ≠ p.2}) → KMachine Γ (FoldStateRev l) ι'
  | [] => haltMachine
  | p :: rest => seq (copyPairsRev rest) (copyStrAtRev p.1.1 p.1.2 p.2) CopyState.copy

end PeriodicTM
