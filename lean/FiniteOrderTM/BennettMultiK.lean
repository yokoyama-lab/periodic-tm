/-
FiniteOrderTM/BennettMultiK.lean

The multi-tape (`ι = Fin k`) Bennett F;C;U wrapper.  Same shape as the single-tape
`bennettBStr` (BennettFCU.lean) but the copy leg is the `k`-fold per-tape copy
`copyMultiK k` (CopyMultiK.lean) instead of the single-tape `copyStrW`, on the
matching bank index `(Fin k ⊕ Fin 1) ⊕ Fin k = (work ⊕ history) ⊕ ancilla`.

Cleaner than the single-tape version: `copyMultiK` is built *natively* on the full
bank, so no `bankEquiv` reindexing is needed and the copy precondition is the clean
`MultiDomIn k` (each work tape an anchored blank-free block, each ancilla blank).

`bennettBStrK_semInverse` ports `bennettBStr_semInverse` verbatim with
`copyStrW → copyMultiK k`, the copy `SemInverse` from `copyMultiK_semInverse`, and
the work⊕history hand-over from `copyMultiK_preserves_left`.  `hCompatI` (the F-leg
output meets `MultiDomIn k`) is left as a parameter, to be discharged
unconditionally for block data in a follow-up via a multi-tape
`phaseF2_forward_correct`.
-/
import FiniteOrderTM.BennettFCU
import FiniteOrderTM.CopyMultiK

namespace PeriodicTM

open Turing

variable {Γ : Type*} [Inhabited Γ] [DecidableEq Γ] {Λ : Type*} [DecidableEq Λ]

/-- The multi-tape full-string Bennett forward;copy;uncompute machine on
`(Fin k ⊕ Fin 1) ⊕ Fin k`. -/
noncomputable def bennettBStrK (k : ℕ) (M₀ : KMachine Γ Λ (Fin k)) :
    KMachine (BennettAlph2 Γ Λ (Fin k))
      ((BennettState2 Γ Λ (Fin k) ⊕ FoldState (tapePairs k)) ⊕ UncompState Γ Λ (Fin k))
      ((Fin k ⊕ Fin 1) ⊕ Fin k) :=
  seq (seq (liftL (phaseF2 M₀) (κ := Fin k))
        (copyMultiK k (Γ := BennettAlph2 Γ Λ (Fin k))) (foldStart (tapePairs k)))
      (liftL (phaseU2 M₀) (κ := Fin k)) UncompState.RStart

/-- The reverse multi-tape Bennett machine: `U⁻¹ ; C⁻¹ ; F⁻¹`. -/
noncomputable def bennettBStrK' (k : ℕ) (M₀ : KMachine Γ Λ (Fin k)) :
    KMachine (BennettAlph2 Γ Λ (Fin k))
      (BennettState2 Γ Λ (Fin k) ⊕ (FoldStateRev (tapePairs k) ⊕ UncompState Γ Λ (Fin k)))
      ((Fin k ⊕ Fin 1) ⊕ Fin k) :=
  seq (liftL (phaseF2 M₀) (κ := Fin k))
      (seq (copyMultiKRev k (Γ := BennettAlph2 Γ Λ (Fin k)))
        (liftL (phaseU2 M₀) (κ := Fin k)) UncompState.RStart)
      (Sum.inl (foldStartRev (tapePairs k)))

/-- Output domain for the multi-tape wrapper: the image of `bennettBStrK`. -/
def DomOutBStrK (k : ℕ) (M₀ : KMachine Γ Λ (Fin k)) (q₀ : Λ)
    (DomIn : ((Fin k ⊕ Fin 1) ⊕ Fin k → Tape (BennettAlph2 Γ Λ (Fin k))) → Prop) :
    ((Fin k ⊕ Fin 1) ⊕ Fin k → Tape (BennettAlph2 Γ Λ (Fin k))) → Prop :=
  fun Y => ∃ X, DomIn X ∧
    Y ∈ ktapeSem (bennettBStrK k M₀) (Sum.inl (Sum.inl (BennettState2.A1 q₀))) X

/-- **The multi-tape Bennett wrapper is semantically reversible**, given a domain
`DomIn` whose work⊕history block is well-formed (`hWF`) and whose F-leg output meets
the multi-tape copy precondition `MultiDomIn k` (`hCompatI`).  Faithful port of
`bennettBStr_semInverse`: F/U legs from `phaseF2_semInverse.liftL`, copy leg from
`copyMultiK_semInverse`, work⊕history hand-over from `copyMultiK_preserves_left`. -/
theorem bennettBStrK_semInverse (k : ℕ) (M₀ : KMachine Γ Λ (Fin k)) (q₀ : Λ)
    (DomIn : ((Fin k ⊕ Fin 1) ⊕ Fin k → Tape (BennettAlph2 Γ Λ (Fin k))) → Prop)
    (hWF : ∀ X, DomIn X → WFblank (X ∘ Sum.inl))
    (hCompatI : ∀ X U, DomIn X →
      U ∈ ktapeSem (liftL (phaseF2 M₀) (κ := Fin k)) (BennettState2.A1 q₀) X →
      MultiDomIn k U) :
    SemInverse (bennettBStrK k M₀) (bennettBStrK' k M₀)
      (Sum.inl (Sum.inl (BennettState2.A1 q₀))) (Sum.inl (BennettState2.A1 q₀))
      DomIn (DomOutBStrK k M₀ q₀ DomIn) := by
  -- forward F-leg: phaseF2 inverts to phaseU2, lifted
  have hFleg : ∀ X U, DomIn X →
      U ∈ ktapeSem (liftL (phaseF2 M₀) (κ := Fin k)) (BennettState2.A1 q₀) X →
      X ∈ ktapeSem (liftL (phaseU2 M₀) (κ := Fin k)) UncompState.RStart U :=
    fun X U hX hU => ((phaseF2_semInverse M₀ q₀).liftL (κ := Fin k)).fwd X U (hWF X hX) hU
  -- inner forward composite F;C (copy precondition supplied by hCompatI)
  have hInner : ∀ X U, DomIn X →
      U ∈ ktapeSem (seq (liftL (phaseF2 M₀) (κ := Fin k))
            (copyMultiK k (Γ := BennettAlph2 Γ Λ (Fin k))) (foldStart (tapePairs k)))
          (Sum.inl (BennettState2.A1 q₀)) X →
      X ∈ ktapeSem (seq (copyMultiKRev k (Γ := BennettAlph2 Γ Λ (Fin k)))
            (liftL (phaseU2 M₀) (κ := Fin k)) UncompState.RStart)
          (Sum.inl (foldStartRev (tapePairs k))) U :=
    fun X U hX hU =>
      SemInverse.fwd_seq hFleg (copyMultiK_semInverse k).fwd hCompatI X U hX hU
  -- forward U-leg: phaseU2 inverts to phaseF2, lifted
  have hUleg : ∀ U Y, reachableOutput M₀ q₀ (U ∘ Sum.inl) →
      Y ∈ ktapeSem (liftL (phaseU2 M₀) (κ := Fin k)) UncompState.RStart U →
      U ∈ ktapeSem (liftL (phaseF2 M₀) (κ := Fin k)) (BennettState2.A1 q₀) Y :=
    fun U Y hU hY => ((phaseU2_semInverse M₀ q₀).liftL (κ := Fin k)).fwd U Y hU hY
  -- after F;C the work⊕history block is a reachable phaseF2 output
  have hCompatO : ∀ X U, DomIn X →
      U ∈ ktapeSem (seq (liftL (phaseF2 M₀) (κ := Fin k))
            (copyMultiK k (Γ := BennettAlph2 Γ Λ (Fin k))) (foldStart (tapePairs k)))
          (Sum.inl (BennettState2.A1 q₀)) X →
      reachableOutput M₀ q₀ (U ∘ Sum.inl) := by
    intro X U hX hU
    rw [ktapeSem_seq, Part.mem_bind_iff] at hU
    obtain ⟨W, hW, hUc⟩ := hU
    have hWl := (ktapeSem_liftL_mem (phaseF2 M₀) (BennettState2.A1 q₀) hW).2
    have hpl : U ∘ Sum.inl = W ∘ Sum.inl :=
      funext (copyMultiK_preserves_left k W U (hCompatI X W hX hW) hUc)
    exact ⟨X ∘ Sum.inl, hWF X hX, by rw [hpl]; exact hWl⟩
  -- assemble the forward implication
  have hfwd : ∀ X Y, DomIn X →
      Y ∈ ktapeSem (bennettBStrK k M₀) (Sum.inl (Sum.inl (BennettState2.A1 q₀))) X →
      X ∈ ktapeSem (bennettBStrK' k M₀) (Sum.inl (BennettState2.A1 q₀)) Y :=
    fun X Y hX hY => SemInverse.fwd_seq hInner hUleg hCompatO X Y hX hY
  exact
    { fwd := hfwd
      bwd := by
        rintro X Y ⟨X₀, hX₀dom, hYB⟩ hX
        rw [Part.mem_unique hX (hfwd X₀ Y hX₀dom hYB)]; exact hYB }

/-! ### Discharging `hCompatI` for multi-tape block data

Each work tape's F-leg output is `Tape.map inlMap (Y0 j)` where `Y0` is `M₀`'s
`k`-tape output (`phaseF2_forward_correct`).  On the domain of inputs whose every
`M₀`-output tape `Y0 j` is an anchored blank-free block, the multi-tape copy
precondition `MultiDomIn k` holds and `bennettBStrK` is unconditionally a
`SemInverse`. -/

/-- Input domain for the multi-tape wrapper: a lifted `k`-tape input `A` with blank
history and blank ancillas, whose `M₀`-output `Y0 j` is an anchored blank-free
block on *every* tape `j` (so each tape meets the copy leg's `CopyDomAt`). -/
def DomInBStrK (k : ℕ) (M₀ : KMachine Γ Λ (Fin k)) (q₀ : Λ) :
    ((Fin k ⊕ Fin 1) ⊕ Fin k → Tape (BennettAlph2 Γ Λ (Fin k))) → Prop :=
  fun X => ∃ A Y0,
    X = withR (fun _ : Fin k => (default : Tape (BennettAlph2 Γ Λ (Fin k)))) (liftWork M₀ A)
    ∧ Y0 ∈ ktapeSem M₀ q₀ A
    ∧ ∀ j : Fin k, (Y0 j).nth (-1) = default
        ∧ ∃ n : ℕ, (∀ i : ℕ, i < n → (Y0 j).nth (i : ℤ) ≠ default)
            ∧ (Y0 j).nth (n : ℤ) = default

/-- **The multi-tape Bennett wrapper is unconditionally a `SemInverse`** on
`DomInBStrK` — inputs whose `M₀`-output is an anchored blank-free block on every
tape.  Discharges `hCompatI` per tape from `phaseF2_forward_correct` (the F-leg
output work bank `j` is `Tape.map inlMap (Y0 j)`), closing the multi-tape milestone. -/
theorem bennettBStrK_semInverse_blockdata (k : ℕ)
    (M₀ : KMachine Γ Λ (Fin k)) (q₀ : Λ) :
    SemInverse (bennettBStrK k M₀) (bennettBStrK' k M₀)
      (Sum.inl (Sum.inl (BennettState2.A1 q₀))) (Sum.inl (BennettState2.A1 q₀))
      (DomInBStrK k M₀ q₀) (DomOutBStrK k M₀ q₀ (DomInBStrK k M₀ q₀)) := by
  refine bennettBStrK_semInverse k M₀ q₀ (DomInBStrK k M₀ q₀) ?_ ?_
  · -- hWF: the work⊕history block is well-formed (it is `liftWork M₀ A`)
    rintro X ⟨A, Y0, rfl, -, -⟩
    exact liftWork_WFblank M₀ A
  · -- hCompatI: the F-output meets `MultiDomIn k` (each tape's `CopyDomAt`)
    rintro X U ⟨A, Y0, rfl, hY0, hblocks⟩ hU
    obtain ⟨hfroz, hleft⟩ := ktapeSem_liftL_mem (phaseF2 M₀) (BennettState2.A1 q₀) hU
    obtain ⟨Y, hYmem, hYwork⟩ := phaseF2_forward_correct M₀ q₀ A Y0 hY0
    have hUY : U ∘ Sum.inl = Y := Part.mem_unique hleft hYmem
    intro j
    obtain ⟨hanchor, n, hblock, hend⟩ := hblocks j
    have hwork : U (Sum.inl (Sum.inl j)) = Tape.map inlMap (Y0 j) := by
      have h := congrFun hUY (Sum.inl j)
      rw [Function.comp_apply] at h
      rw [h, hYwork j]
    have hanc : U (Sum.inr j) = (default : Tape (BennettAlph2 Γ Λ (Fin k))) := by
      have h := congrFun hfroz j
      simpa [withR] using h
    refine ⟨?_, ?_, n, ?_, ?_⟩
    · -- anchor at -1 on work tape j
      show (U (Sum.inl (Sum.inl j))).nth (-1) = default
      rw [hwork, Tape.map_nth]
      exact congrArg Sum.inl hanchor
    · -- ancilla tape j all blank
      intro m
      show (U (Sum.inr j)).nth m = default
      rw [hanc]; exact Tape.nth_default m
    · -- blank-free block on work tape j
      intro i hi
      show (U (Sum.inl (Sum.inl j))).nth (i : ℤ) ≠ default
      rw [hwork, Tape.map_nth]
      intro hcon
      apply hblock i hi
      have h2 : (Sum.inl ((Y0 j).nth (i : ℤ)) : BennettAlph2 Γ Λ (Fin k))
          = Sum.inl default := hcon
      exact Sum.inl.inj h2
    · -- terminating blank on work tape j
      show (U (Sum.inl (Sum.inl j))).nth (n : ℤ) = default
      rw [hwork, Tape.map_nth]
      exact congrArg Sum.inl hend

end PeriodicTM
