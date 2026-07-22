/-
# The Bennett F;C;U wrapper, assembled (R1 G2 architecture, A2b)

`bennettB = liftL phaseF2 ; copyWA ; liftL phaseU2` on the common bank index
`(ι ⊕ Fin 1) ⊕ ι` = (work ⊕ history) ⊕ ancilla.  Its semantic inverse is
`bennettB' = liftL phaseF2 ; copyWArev ; liftL phaseU2` (the reverse composition
`U⁻¹ ; C⁻¹ ; F⁻¹`, where `phaseF2` inverts `phaseU2` and vice versa).

`bennettB_semInverse` proves `SemInverse bennettB bennettB'` on the input domain
`DomInB` (work⊕history a well-formed blank-initialised `phaseF2` input, ancilla
blank) and the *image* output domain `DomOutB`.  The proof mirrors
`phaseF2_semInverse`: the forward leg is a `fwd_seq ∘ fwd_seq` composition
(needing only the input-side hand-overs, discharged by the frozen-bank
preservation lemmas), and the backward leg is `Part.mem_unique` against the image
domain.  This is the single-cell (head-valued) version; the full-string
traversal copy is left for later.
-/
import FiniteOrderTM.Copy
import FiniteOrderTM.BennettUncompute
import FiniteOrderTM.Unconditional

namespace PeriodicTM

open Turing

variable {Γ : Type*} [Inhabited Γ] [DecidableEq Γ] {Λ : Type*} {ι : Type*}

/-- The Bennett forward;copy;uncompute machine on `(ι ⊕ Fin 1) ⊕ ι`. -/
noncomputable def bennettB (M₀ : KMachine Γ Λ ι) :
    KMachine (BennettAlph2 Γ Λ ι)
      ((BennettState2 Γ Λ ι ⊕ Bool) ⊕ UncompState Γ Λ ι)
      ((ι ⊕ Fin 1) ⊕ ι) :=
  seq (seq (liftL (phaseF2 M₀) (κ := ι))
        (copyWA (Γ := BennettAlph2 Γ Λ ι) (ι := ι) (τ := Fin 1)) false)
      (liftL (phaseU2 M₀) (κ := ι)) UncompState.RStart

/-- The reverse Bennett machine: `U⁻¹ ; C⁻¹ ; F⁻¹`. -/
noncomputable def bennettB' (M₀ : KMachine Γ Λ ι) :
    KMachine (BennettAlph2 Γ Λ ι)
      (BennettState2 Γ Λ ι ⊕ (Bool ⊕ UncompState Γ Λ ι))
      ((ι ⊕ Fin 1) ⊕ ι) :=
  seq (liftL (phaseF2 M₀) (κ := ι))
      (seq (copyWArev (Γ := BennettAlph2 Γ Λ ι) (ι := ι) (τ := Fin 1))
        (liftL (phaseU2 M₀) (κ := ι)) UncompState.RStart)
      (Sum.inl false)

/-! ### Full-string variant: `bennettBStr`

The single-tape (`ι = Unit`) wrapper with the full-string traversal copy
`copyStrW` in place of the single-cell `copyWA`.  Same F;C;U shape; the copy leg
now duplicates an entire blank-free block (not just the head cell), so this is the
general-data version.  Requires `[DecidableEq Λ]` to run `copyStr` at the wrapper
alphabet `BennettAlph2 Γ Λ Unit`. -/

/-- The full-string Bennett forward;copy;uncompute machine on `(Unit ⊕ Fin 1) ⊕ Unit`. -/
noncomputable def bennettBStr [DecidableEq Λ] (M₀ : KMachine Γ Λ Unit) :
    KMachine (BennettAlph2 Γ Λ Unit)
      ((BennettState2 Γ Λ Unit ⊕ CopyState) ⊕ UncompState Γ Λ Unit)
      ((Unit ⊕ Fin 1) ⊕ Unit) :=
  seq (seq (liftL (phaseF2 M₀) (κ := Unit))
        (copyStrW (Γ := BennettAlph2 Γ Λ Unit)) CopyState.copy)
      (liftL (phaseU2 M₀) (κ := Unit)) UncompState.RStart

/-- The reverse full-string Bennett machine: `U⁻¹ ; C⁻¹ ; F⁻¹`. -/
noncomputable def bennettBStr' [DecidableEq Λ] (M₀ : KMachine Γ Λ Unit) :
    KMachine (BennettAlph2 Γ Λ Unit)
      (BennettState2 Γ Λ Unit ⊕ (CopyState ⊕ UncompState Γ Λ Unit))
      ((Unit ⊕ Fin 1) ⊕ Unit) :=
  seq (liftL (phaseF2 M₀) (κ := Unit))
      (seq (copyStrWrev (Γ := BennettAlph2 Γ Λ Unit))
        (liftL (phaseU2 M₀) (κ := Unit)) UncompState.RStart)
      (Sum.inl CopyState.copy)

/-- Input domain: the work⊕history block is a well-formed blank-initialised
`phaseF2` input, and the ancilla is blank. -/
def DomInB (M₀ : KMachine Γ Λ ι) :
    ((ι ⊕ Fin 1) ⊕ ι → Tape (BennettAlph2 Γ Λ ι)) → Prop :=
  fun X => WFblank (X ∘ Sum.inl) ∧ AncBlank X

/-- Output domain: the image of `bennettB` from `DomInB` inputs. -/
def DomOutB (M₀ : KMachine Γ Λ ι) (q₀ : Λ) :
    ((ι ⊕ Fin 1) ⊕ ι → Tape (BennettAlph2 Γ Λ ι)) → Prop :=
  fun Y => ∃ X, DomInB M₀ X ∧
    Y ∈ ktapeSem (bennettB M₀) (Sum.inl (Sum.inl (BennettState2.A1 q₀))) X

/-- **A2b: the Bennett F;C;U wrapper is semantically reversible.**
`bennettB'` semantically inverts `bennettB` on `DomInB`/`DomOutB`. -/
theorem bennettB_semInverse (M₀ : KMachine Γ Λ ι) (q₀ : Λ) :
    SemInverse (bennettB M₀) (bennettB' M₀)
      (Sum.inl (Sum.inl (BennettState2.A1 q₀))) (Sum.inl (BennettState2.A1 q₀))
      (DomInB M₀) (DomOutB M₀ q₀) := by
  -- forward F-leg: phaseF2 inverts to phaseU2, lifted, on DomInB
  have hFleg : ∀ X U, DomInB M₀ X →
      U ∈ ktapeSem (liftL (phaseF2 M₀) (κ := ι)) (BennettState2.A1 q₀) X →
      X ∈ ktapeSem (liftL (phaseU2 M₀) (κ := ι)) UncompState.RStart U :=
    fun X U hX hU => ((phaseF2_semInverse M₀ q₀).liftL (κ := ι)).fwd X U hX.1 hU
  -- F freezes the ancilla, so its output keeps the ancilla blank
  have hCompatI : ∀ X U, DomInB M₀ X →
      U ∈ ktapeSem (liftL (phaseF2 M₀) (κ := ι)) (BennettState2.A1 q₀) X →
      AncBlank U := by
    intro X U hX hU t
    have hr := (ktapeSem_liftL_mem (phaseF2 M₀) (BennettState2.A1 q₀) hU).1
    have hUt : U (Sum.inr t) = X (Sum.inr t) := congrFun hr t
    rw [hUt]; exact hX.2 t
  -- inner forward composite F;C
  have hInner : ∀ X U, DomInB M₀ X →
      U ∈ ktapeSem (seq (liftL (phaseF2 M₀) (κ := ι))
            (copyWA (Γ := BennettAlph2 Γ Λ ι) (ι := ι) (τ := Fin 1)) false)
          (Sum.inl (BennettState2.A1 q₀)) X →
      X ∈ ktapeSem (seq (copyWArev (Γ := BennettAlph2 Γ Λ ι) (ι := ι) (τ := Fin 1))
            (liftL (phaseU2 M₀) (κ := ι)) UncompState.RStart)
          (Sum.inl false) U :=
    fun X U hX hU =>
      SemInverse.fwd_seq hFleg copyWA_semInverse.fwd hCompatI X U hX hU
  -- forward U-leg: phaseU2 inverts to phaseF2, lifted
  have hUleg : ∀ U Y, reachableOutput M₀ q₀ (U ∘ Sum.inl) →
      Y ∈ ktapeSem (liftL (phaseU2 M₀) (κ := ι)) UncompState.RStart U →
      U ∈ ktapeSem (liftL (phaseF2 M₀) (κ := ι)) (BennettState2.A1 q₀) Y :=
    fun U Y hU hY => ((phaseU2_semInverse M₀ q₀).liftL (κ := ι)).fwd U Y hU hY
  -- after F;C the work⊕history block is a reachable phaseF2 output
  have hCompatO : ∀ X U, DomInB M₀ X →
      U ∈ ktapeSem (seq (liftL (phaseF2 M₀) (κ := ι))
            (copyWA (Γ := BennettAlph2 Γ Λ ι) (ι := ι) (τ := Fin 1)) false)
          (Sum.inl (BennettState2.A1 q₀)) X →
      reachableOutput M₀ q₀ (U ∘ Sum.inl) := by
    intro X U hX hU
    rw [ktapeSem_seq, Part.mem_bind_iff] at hU
    obtain ⟨W, hW, hUc⟩ := hU
    have hWl := (ktapeSem_liftL_mem (phaseF2 M₀) (BennettState2.A1 q₀) hW).2
    have hpl : U ∘ Sum.inl = W ∘ Sum.inl := funext (copyWA_preserves_left hUc)
    exact ⟨X ∘ Sum.inl, hX.1, by rw [hpl]; exact hWl⟩
  -- assemble the forward implication for B
  have hfwd : ∀ X Y, DomInB M₀ X →
      Y ∈ ktapeSem (bennettB M₀) (Sum.inl (Sum.inl (BennettState2.A1 q₀))) X →
      X ∈ ktapeSem (bennettB' M₀) (Sum.inl (BennettState2.A1 q₀)) Y :=
    fun X Y hX hY => SemInverse.fwd_seq hInner hUleg hCompatO X Y hX hY
  exact
    { fwd := hfwd
      bwd := by
        rintro X Y ⟨X₀, hX₀dom, hYB⟩ hX
        rw [Part.mem_unique hX (hfwd X₀ Y hX₀dom hYB)]; exact hYB }

/-- Output domain for the full-string wrapper: the image of `bennettBStr` from a
given input domain `DomIn`. -/
def DomOutBStr [DecidableEq Λ] (M₀ : KMachine Γ Λ Unit) (q₀ : Λ)
    (DomIn : ((Unit ⊕ Fin 1) ⊕ Unit → Tape (BennettAlph2 Γ Λ Unit)) → Prop) :
    ((Unit ⊕ Fin 1) ⊕ Unit → Tape (BennettAlph2 Γ Λ Unit)) → Prop :=
  fun Y => ∃ X, DomIn X ∧
    Y ∈ ktapeSem (bennettBStr M₀) (Sum.inl (Sum.inl (BennettState2.A1 q₀))) X

/-- **step5: the full-string Bennett wrapper is semantically reversible**, given an
input domain `DomIn` whose work⊕history block is well-formed (`hWF`) and whose
F-leg output's work bank is an anchored blank-free block, so `copyStrW`'s
`CopyDomIn` holds (`hCompatI`).  `hCompatI` is the single remaining obligation
(step5b: a characterization of `phaseF2`'s output as blank-free, dischargeable by a
strong enough `DomIn`).  Everything else — the F/U legs, the full-string copy
`SemInverse`, and the work-block hand-over — is discharged here, exactly mirroring
`bennettB_semInverse` with `copyWA` replaced by the traversal copy `copyStrW`. -/
theorem bennettBStr_semInverse [DecidableEq Λ] (M₀ : KMachine Γ Λ Unit) (q₀ : Λ)
    (DomIn : ((Unit ⊕ Fin 1) ⊕ Unit → Tape (BennettAlph2 Γ Λ Unit)) → Prop)
    (hWF : ∀ X, DomIn X → WFblank (X ∘ Sum.inl))
    (hCompatI : ∀ X U, DomIn X →
      U ∈ ktapeSem (liftL (phaseF2 M₀) (κ := Unit)) (BennettState2.A1 q₀) X →
      CopyDomIn (fun i => U (bankEquiv (Sum.inl i)))) :
    SemInverse (bennettBStr M₀) (bennettBStr' M₀)
      (Sum.inl (Sum.inl (BennettState2.A1 q₀))) (Sum.inl (BennettState2.A1 q₀))
      DomIn (DomOutBStr M₀ q₀ DomIn) := by
  -- forward F-leg: phaseF2 inverts to phaseU2, lifted
  have hFleg : ∀ X U, DomIn X →
      U ∈ ktapeSem (liftL (phaseF2 M₀) (κ := Unit)) (BennettState2.A1 q₀) X →
      X ∈ ktapeSem (liftL (phaseU2 M₀) (κ := Unit)) UncompState.RStart U :=
    fun X U hX hU => ((phaseF2_semInverse M₀ q₀).liftL (κ := Unit)).fwd X U (hWF X hX) hU
  -- inner forward composite F;C (copy precondition supplied by hCompatI)
  have hInner : ∀ X U, DomIn X →
      U ∈ ktapeSem (seq (liftL (phaseF2 M₀) (κ := Unit))
            (copyStrW (Γ := BennettAlph2 Γ Λ Unit)) CopyState.copy)
          (Sum.inl (BennettState2.A1 q₀)) X →
      X ∈ ktapeSem (seq (copyStrWrev (Γ := BennettAlph2 Γ Λ Unit))
            (liftL (phaseU2 M₀) (κ := Unit)) UncompState.RStart)
          (Sum.inl CopyState.copy) U :=
    fun X U hX hU =>
      SemInverse.fwd_seq hFleg (copyStrW_semInverse (Γ := BennettAlph2 Γ Λ Unit)).fwd
        hCompatI X U hX hU
  -- forward U-leg: phaseU2 inverts to phaseF2, lifted
  have hUleg : ∀ U Y, reachableOutput M₀ q₀ (U ∘ Sum.inl) →
      Y ∈ ktapeSem (liftL (phaseU2 M₀) (κ := Unit)) UncompState.RStart U →
      U ∈ ktapeSem (liftL (phaseF2 M₀) (κ := Unit)) (BennettState2.A1 q₀) Y :=
    fun U Y hU hY => ((phaseU2_semInverse M₀ q₀).liftL (κ := Unit)).fwd U Y hU hY
  -- after F;C the work⊕history block is a reachable phaseF2 output
  have hCompatO : ∀ X U, DomIn X →
      U ∈ ktapeSem (seq (liftL (phaseF2 M₀) (κ := Unit))
            (copyStrW (Γ := BennettAlph2 Γ Λ Unit)) CopyState.copy)
          (Sum.inl (BennettState2.A1 q₀)) X →
      reachableOutput M₀ q₀ (U ∘ Sum.inl) := by
    intro X U hX hU
    rw [ktapeSem_seq, Part.mem_bind_iff] at hU
    obtain ⟨W, hW, hUc⟩ := hU
    have hWl := (ktapeSem_liftL_mem (phaseF2 M₀) (BennettState2.A1 q₀) hW).2
    have hpl : U ∘ Sum.inl = W ∘ Sum.inl :=
      funext (copyStrW_preserves_left W U (hCompatI X W hX hW) hUc)
    exact ⟨X ∘ Sum.inl, hWF X hX, by rw [hpl]; exact hWl⟩
  -- assemble the forward implication
  have hfwd : ∀ X Y, DomIn X →
      Y ∈ ktapeSem (bennettBStr M₀) (Sum.inl (Sum.inl (BennettState2.A1 q₀))) X →
      X ∈ ktapeSem (bennettBStr' M₀) (Sum.inl (BennettState2.A1 q₀)) Y :=
    fun X Y hX hY => SemInverse.fwd_seq hInner hUleg hCompatO X Y hX hY
  exact
    { fwd := hfwd
      bwd := by
        rintro X Y ⟨X₀, hX₀dom, hYB⟩ hX
        rw [Part.mem_unique hX (hfwd X₀ Y hX₀dom hYB)]; exact hYB }

/-! ### Discharging `hCompatI` for blank-free single-tape data (step5b)

The F-leg output's work bank is `Tape.map inlMap (Y0 ())` where `Y0` is `M₀`'s
output (`phaseF2_forward_correct`).  Since `(Tape.map inlMap T).nth m = Sum.inl
(T.nth m)`, that work bank is an anchored blank-free block exactly when `M₀`'s
output `Y0 ()` is — so on the domain of inputs whose `M₀`-output is an anchored
blank-free block, `hCompatI` holds and `bennettBStr` is unconditionally a
`SemInverse`. -/

/-- `Tape.map` acts cellwise on `nth`. -/
theorem Tape.map_nth {Δ Δ' : Type*} [Inhabited Δ] [Inhabited Δ']
    (f : PointedMap Δ Δ') (T : Tape Δ) :
    ∀ m : ℤ, (T.map f).nth m = f (T.nth m)
  | 0 => rfl
  | (n + 1 : ℕ) => ListBlank.nth_map f _ n
  | -(n + 1 : ℕ) => ListBlank.nth_map f _ n

/-- The blank `ListBlank` reads `default` at every position. -/
theorem ListBlank.nth_default {Δ : Type*} [Inhabited Δ] (n : ℕ) :
    (default : ListBlank Δ).nth n = default := by
  show ListBlank.nth (ListBlank.mk []) n = default
  rw [ListBlank.nth_mk]; simp

/-- The blank tape reads `default` at every position. -/
theorem Tape.nth_default {Δ : Type*} [Inhabited Δ] :
    ∀ m : ℤ, (default : Tape Δ).nth m = default
  | 0 => rfl
  | (n + 1 : ℕ) => ListBlank.nth_default n
  | -(n + 1 : ℕ) => ListBlank.nth_default n

/-- Input domain for the full-string wrapper: a lifted single-tape input `A` with
blank history and blank ancilla, whose `M₀`-output `Y0 ()` is an anchored
blank-free block (so the copy leg's `CopyDomIn` is met). -/
def DomInBStr (M₀ : KMachine Γ Λ Unit) (q₀ : Λ) :
    ((Unit ⊕ Fin 1) ⊕ Unit → Tape (BennettAlph2 Γ Λ Unit)) → Prop :=
  fun X => ∃ A Y0,
    X = withR (fun _ : Unit => (default : Tape (BennettAlph2 Γ Λ Unit))) (liftWork M₀ A)
    ∧ Y0 ∈ ktapeSem M₀ q₀ A
    ∧ (Y0 ()).nth (-1) = default
    ∧ ∃ n : ℕ, (∀ i : ℕ, i < n → (Y0 ()).nth (i : ℤ) ≠ default)
        ∧ (Y0 ()).nth (n : ℤ) = default

/-- **step5 (general data): the full-string Bennett wrapper is unconditionally a
`SemInverse`** on `DomInBStr` — inputs whose `M₀`-output is an anchored blank-free
block.  This discharges `hCompatI` from `phaseF2_forward_correct` (the F-leg output
work bank is `Tape.map inlMap (Y0 ())`) and closes the full-string milestone. -/
theorem bennettBStr_semInverse_blockdata [DecidableEq Λ]
    (M₀ : KMachine Γ Λ Unit) (q₀ : Λ) :
    SemInverse (bennettBStr M₀) (bennettBStr' M₀)
      (Sum.inl (Sum.inl (BennettState2.A1 q₀))) (Sum.inl (BennettState2.A1 q₀))
      (DomInBStr M₀ q₀) (DomOutBStr M₀ q₀ (DomInBStr M₀ q₀)) := by
  refine bennettBStr_semInverse M₀ q₀ (DomInBStr M₀ q₀) ?_ ?_
  · -- hWF: the work⊕history block is well-formed (it is `liftWork M₀ A`)
    rintro X ⟨A, Y0, rfl, -, -, -⟩
    exact liftWork_WFblank M₀ A
  · -- hCompatI: the F-output work bank ∈ CopyDomIn
    rintro X U ⟨A, Y0, rfl, hY0, hanchor, n, hblock, hend⟩ hU
    obtain ⟨hfroz, hleft⟩ := ktapeSem_liftL_mem (phaseF2 M₀) (BennettState2.A1 q₀) hU
    obtain ⟨Y, hYmem, hYwork⟩ := phaseF2_forward_correct M₀ q₀ A Y0 hY0
    have hUY : U ∘ Sum.inl = Y := Part.mem_unique hleft hYmem
    have hwork : U (Sum.inl (Sum.inl ())) = Tape.map inlMap (Y0 ()) := by
      have h := congrFun hUY (Sum.inl ())
      rw [Function.comp_apply] at h
      rw [h, hYwork ()]
    have hanc : U (Sum.inr ()) = (default : Tape (BennettAlph2 Γ Λ Unit)) := by
      have h := congrFun hfroz ()
      simpa [withR] using h
    refine ⟨?_, ?_, n, ?_, ?_⟩
    · -- anchor at -1
      show (U (Sum.inl (Sum.inl ()))).nth (-1) = default
      rw [hwork, Tape.map_nth]
      exact congrArg Sum.inl hanchor
    · -- target all blank
      intro m
      show (U (Sum.inr ())).nth m = default
      rw [hanc]; exact Tape.nth_default m
    · -- blank-free block
      intro i hi
      show (U (Sum.inl (Sum.inl ()))).nth (i : ℤ) ≠ default
      rw [hwork, Tape.map_nth]
      intro hcon
      apply hblock i hi
      have h2 : (Sum.inl ((Y0 ()).nth (i : ℤ)) : BennettAlph2 Γ Λ Unit)
          = Sum.inl default := hcon
      exact Sum.inl.inj h2
    · -- terminating blank
      show (U (Sum.inl (Sum.inl ()))).nth (n : ℤ) = default
      rw [hwork, Tape.map_nth]
      exact congrArg Sum.inl hend

/-- **A3: the Bennett wrapper computes `M₀` onto the ancilla.**  On a lifted input
`liftWork A` with blank ancilla, `bennettB` halts with the work⊕history block
restored to the input and the ancilla head holding the answer head: if `M₀` maps
`A` to `Y0`, then `(output ancilla j).head = Sum.inl (Y0 j).head`.  This is the
single-cell (head-valued) correctness; it feeds the work↔ancilla swap in A5. -/
theorem bennettB_correct (M₀ : KMachine Γ Λ ι) (q₀ : Λ) (A Y0 : ι → Tape Γ)
    (hY0 : Y0 ∈ ktapeSem M₀ q₀ A) :
    ∃ Z, Z ∈ ktapeSem (bennettB M₀) (Sum.inl (Sum.inl (BennettState2.A1 q₀)))
            (withR (fun _ : ι => (default : Tape (BennettAlph2 Γ Λ ι)))
              (liftWork M₀ A)) ∧
         (∀ j, Z (Sum.inl (Sum.inl j)) = Tape.map inlMap (A j)) ∧
         (∀ j, (Z (Sum.inr j)).1 = Sum.inl ((Y0 j).1)) := by
  classical
  -- F-leg: phaseF2 computes M₀'s function onto the work banks
  obtain ⟨Y, hY, hYwork⟩ := phaseF2_forward_correct M₀ q₀ A Y0 hY0
  -- F output (ancilla frozen blank)
  set Uf : (ι ⊕ Fin 1) ⊕ ι → Tape (BennettAlph2 Γ Λ ι) :=
    withR (fun _ : ι => (default : Tape (BennettAlph2 Γ Λ ι))) Y with hUf
  have hUfmem : Uf ∈ ktapeSem (liftL (phaseF2 M₀) (κ := ι))
      (BennettState2.A1 q₀)
      (withR (fun _ : ι => (default : Tape (BennettAlph2 Γ Λ ι)))
        (liftWork M₀ A)) := by
    rw [ktapeSem_liftL, Part.mem_map_iff]
    exact ⟨Y, hY, rfl⟩
  -- C-leg: copy work heads onto the ancilla
  obtain ⟨W, hWmem⟩ :
      ∃ W, W ∈ ktapeSem (copyWA (Γ := BennettAlph2 Γ Λ ι) (ι := ι) (τ := Fin 1))
        false Uf :=
    ⟨_, (singleWrite_ktapeSem copyWA _ (fun _ => rfl) (fun _ => rfl) Uf _).mpr rfl⟩
  have hWpl : ∀ x, W (Sum.inl x) = Uf (Sum.inl x) := copyWA_preserves_left hWmem
  have hWanc : AncMatchesWork W := copyWA_anc hWmem
  -- the work⊕history block fed to U is exactly the phaseF2 output Y
  have hWinlY : W ∘ Sum.inl = Y := by
    funext x; show W (Sum.inl x) = Y x; rw [hWpl x]; rfl
  -- U-leg: phaseU2 uncomputes the work⊕history block back to the input
  have hUuncompute : liftWork M₀ A ∈
      ktapeSem (phaseU2 M₀) UncompState.RStart (W ∘ Sum.inl) := by
    rw [hWinlY]
    exact (phaseF2_semInverse M₀ q₀).fwd (liftWork M₀ A) Y
      (liftWork_WFblank M₀ A) hY
  set Z : (ι ⊕ Fin 1) ⊕ ι → Tape (BennettAlph2 Γ Λ ι) :=
    withR (W ∘ Sum.inr) (liftWork M₀ A) with hZ
  have hZmem_U : Z ∈ ktapeSem (liftL (phaseU2 M₀) (κ := ι)) UncompState.RStart W := by
    rw [show W = withR (W ∘ Sum.inr) (W ∘ Sum.inl) from (Sum.elim_comp_inl_inr W).symm,
        ktapeSem_liftL, Part.mem_map_iff]
    exact ⟨liftWork M₀ A, hUuncompute, rfl⟩
  refine ⟨Z, ?_, ?_, ?_⟩
  · -- Z ∈ ⟦bennettB⟧
    rw [bennettB, ktapeSem_seq, Part.mem_bind_iff]
    refine ⟨W, ?_, hZmem_U⟩
    rw [ktapeSem_seq, Part.mem_bind_iff]
    exact ⟨Uf, hUfmem, hWmem⟩
  · -- work⊕history restored to the input
    intro j; rfl
  · -- ancilla head = lifted answer head
    intro j
    have h2 : (W (Sum.inr j)).1 = (W (Sum.inl (Sum.inl j))).1 := hWanc j
    have h3 : W (Sum.inl (Sum.inl j)) = Y (Sum.inl j) := by
      rw [hWpl (Sum.inl j)]; rfl
    show (W (Sum.inr j)).1 = Sum.inl ((Y0 j).1)
    rw [h2, h3, hYwork j, Tape.map_fst]; rfl

/-! ### The work↔ancilla swap (middle leg of the conjugation `D = B ; swap ; B'`)

`conj_isPartialInvolution` conjugates a `KInvolutory` middle machine by the
Bennett reversibiliser.  For the F;C;U wrapper the middle machine is the bank
permutation exchanging the work block `Sum.inl (Sum.inl j)` with the ancilla
`Sum.inr j` (history `Sum.inl (Sum.inr h)` fixed).  This piece is forced
regardless of how the final assembly's domain is scoped. -/

/-- The work↔ancilla bank involution on `(ι ⊕ Fin 1) ⊕ ι`. -/
def wAncMap : ((ι ⊕ Fin 1) ⊕ ι) → ((ι ⊕ Fin 1) ⊕ ι)
  | Sum.inl (Sum.inl j) => Sum.inr j
  | Sum.inl (Sum.inr h) => Sum.inl (Sum.inr h)
  | Sum.inr j => Sum.inl (Sum.inl j)

theorem wAncMap_involutive : Function.Involutive (wAncMap (ι := ι)) := by
  intro x; rcases x with (j | h) | j <;> rfl

/-- The work↔ancilla swap as a self-inverse permutation. -/
def wAncSwap : Equiv.Perm ((ι ⊕ Fin 1) ⊕ ι) :=
  Function.Involutive.toPerm wAncMap wAncMap_involutive

theorem wAncSwap_selfInverse : (wAncSwap (ι := ι))⁻¹ = wAncSwap (ι := ι) :=
  Equiv.ext fun _ => rfl

/-- The work↔ancilla swap machine is `KInvolutory` — the middle leg `M` of the
Bennett conjugation `D = bennettB ; swap ; bennettB'`. -/
theorem involutory_wAncSwap :
    KInvolutory (Γ := BennettAlph2 Γ Λ ι) (bankSwap (wAncSwap (ι := ι)))
      Bool.not false true :=
  involutory_bankSwap (Γ := BennettAlph2 Γ Λ ι) (wAncSwap (ι := ι))
    wAncSwap_selfInverse

/-! ### Single-cell (head-valued) data — foundation for the A5 assembly (Option B)

The conjugation `D = B ; swap ; B'` computes a partial involution only when the
swapped output `swap(B-output)` is itself a `B`-output (the `hdom` obligation).
With the single-cell copy `copyWA`, the ancilla holds only the *head* of the
answer, so this round-trips exactly on **head-valued** data: tapes blank
everywhere except the head.  `IsCell` names that class; `cell_lift` is the key
bridge equality `copyWA`'s ancilla write equals `liftWork` of a single-cell tape.
-/

/-- Lifting the blank tape is the blank tape. -/
theorem map_inlMap_default :
    Tape.map (inlMap : PointedMap Γ (BennettAlph2 Γ Λ ι)) default = default := rfl

/-- **Single-cell bridge.**  `copyWA`'s ancilla write `default.write (Sum.inl c)`
is exactly the lift of the single-cell tape `default.write c`.  This is what makes
`swap(B-output)` a `B`-input on head-valued data. -/
theorem cell_lift (c : Γ) :
    (default : Tape (BennettAlph2 Γ Λ ι)).write (Sum.inl c)
      = Tape.map (inlMap : PointedMap Γ (BennettAlph2 Γ Λ ι))
          ((default : Tape Γ).write c) := by
  rw [Tape.map_write]; rfl

/-- A single-cell (head-valued) tape: blank everywhere except its head. -/
def IsCell (T : Tape Γ) : Prop := T = (default : Tape Γ).write T.1

theorem isCell_default : IsCell (default : Tape Γ) := (Tape.write_self default).symm

theorem isCell_write (a : Γ) : IsCell ((default : Tape Γ).write a) := rfl

/-- `IsCell` is preserved by lifting into the Bennett alphabet. -/
theorem isCell_map {T : Tape Γ} (h : IsCell T) :
    IsCell (Tape.map (inlMap : PointedMap Γ (BennettAlph2 Γ Λ ι)) T) := by
  unfold IsCell
  rw [Tape.map_fst]
  conv_lhs => rw [h]
  rw [Tape.map_write]
  rfl

/-- **The reverse leg `B'` blanks the ancilla and restores the work.**  `B'` runs
`phaseF2 ; copyWArev ; phaseU2`: on a work block `liftWork U` (with `M₀` halting
on `U`) and a *single-cell* ancilla `S`, it computes the descriptor of `M₀ U`,
blanks the (single-cell) ancilla, and uncomputes the work back to `liftWork U`.
The output is `liftWork U` with a blank ancilla, independent of `S`'s content.
This is the `B'`-analogue of `bennettB_correct`, all forward. -/
theorem bennettB'_blanks (M₀ : KMachine Γ Λ ι) (q₀ : Λ) (U T : ι → Tape Γ)
    (hUT : T ∈ ktapeSem M₀ q₀ U)
    (S : ι → Tape (BennettAlph2 Γ Λ ι)) (hS : ∀ j, IsCell (S j)) :
    withR (fun _ : ι => (default : Tape (BennettAlph2 Γ Λ ι))) (liftWork M₀ U)
      ∈ ktapeSem (bennettB' M₀) (Sum.inl (BennettState2.A1 q₀))
          (withR S (liftWork M₀ U)) := by
  classical
  obtain ⟨Y, hY, _hYwork⟩ := phaseF2_forward_correct M₀ q₀ U T hUT
  -- F'-leg (ancilla S frozen)
  set Uf : (ι ⊕ Fin 1) ⊕ ι → Tape (BennettAlph2 Γ Λ ι) := withR S Y with hUf
  have hUfmem : Uf ∈ ktapeSem (liftL (phaseF2 M₀) (κ := ι)) (BennettState2.A1 q₀)
      (withR S (liftWork M₀ U)) := by
    rw [ktapeSem_liftL, Part.mem_map_iff]
    exact ⟨Y, hY, rfl⟩
  -- copyWArev-leg: blanks the (single-cell) ancilla, frees the work
  obtain ⟨W, hWmem⟩ :
      ∃ W, W ∈ ktapeSem (copyWArev (Γ := BennettAlph2 Γ Λ ι) (ι := ι) (τ := Fin 1))
        false Uf :=
    ⟨_, (singleWrite_ktapeSem copyWArev _ (fun _ => rfl) (fun _ => rfl) Uf _).mpr rfl⟩
  have hWinlY : W ∘ Sum.inl = Y := by
    funext x; show W (Sum.inl x) = Y x
    rw [copyWArev_preserves_left hWmem x]; rfl
  have hWinr : ∀ j, W (Sum.inr j) = default :=
    copyWArev_blanks hWmem (fun j => hS j)
  -- U'-leg: phaseU2 uncomputes the descriptor back to liftWork U
  have hUuncompute : liftWork M₀ U ∈
      ktapeSem (phaseU2 M₀) UncompState.RStart (W ∘ Sum.inl) := by
    rw [hWinlY]
    exact (phaseF2_semInverse M₀ q₀).fwd (liftWork M₀ U) Y
      (liftWork_WFblank M₀ U) hY
  have hanc : (fun _ : ι => (default : Tape (BennettAlph2 Γ Λ ι))) = W ∘ Sum.inr := by
    funext j; exact (hWinr j).symm
  rw [bennettB', ktapeSem_seq, Part.mem_bind_iff]
  refine ⟨Uf, hUfmem, ?_⟩
  rw [ktapeSem_seq, Part.mem_bind_iff]
  refine ⟨W, hWmem, ?_⟩
  rw [show W = withR (W ∘ Sum.inr) (W ∘ Sum.inl) from (Sum.elim_comp_inl_inr W).symm,
      ktapeSem_liftL, Part.mem_map_iff]
  refine ⟨liftWork M₀ U, hUuncompute, ?_⟩
  rw [← hanc]

/-- **Exact `bennettB` output** on a lifted, head-valued input.  Strengthens
`bennettB_correct`: when `M₀` maps `A` to a *single-cell* `U`, the work block is
restored to `liftWork A` and the ancilla holds `liftWork U` exactly (the
single-cell answer). -/
theorem bennettB_correct_full (M₀ : KMachine Γ Λ ι) (q₀ : Λ) (A U : ι → Tape Γ)
    (hU : ∀ j, IsCell (U j)) (hAU : U ∈ ktapeSem M₀ q₀ A) :
    withR (fun j => liftWork M₀ U (Sum.inl j)) (liftWork M₀ A)
      ∈ ktapeSem (bennettB M₀) (Sum.inl (Sum.inl (BennettState2.A1 q₀)))
          (withR (fun _ : ι => (default : Tape (BennettAlph2 Γ Λ ι)))
            (liftWork M₀ A)) := by
  classical
  obtain ⟨Y, hY, hYwork⟩ := phaseF2_forward_correct M₀ q₀ A U hAU
  set Uf : (ι ⊕ Fin 1) ⊕ ι → Tape (BennettAlph2 Γ Λ ι) :=
    withR (fun _ : ι => (default : Tape (BennettAlph2 Γ Λ ι))) Y with hUf
  have hUfmem : Uf ∈ ktapeSem (liftL (phaseF2 M₀) (κ := ι)) (BennettState2.A1 q₀)
      (withR (fun _ : ι => (default : Tape (BennettAlph2 Γ Λ ι))) (liftWork M₀ A)) := by
    rw [ktapeSem_liftL, Part.mem_map_iff]
    exact ⟨Y, hY, rfl⟩
  obtain ⟨W, hWmem⟩ :
      ∃ W, W ∈ ktapeSem (copyWA (Γ := BennettAlph2 Γ Λ ι) (ι := ι) (τ := Fin 1))
        false Uf :=
    ⟨_, (singleWrite_ktapeSem copyWA _ (fun _ => rfl) (fun _ => rfl) Uf _).mpr rfl⟩
  have hWinlY : W ∘ Sum.inl = Y := by
    funext x; show W (Sum.inl x) = Y x
    rw [copyWA_preserves_left hWmem x]; rfl
  have hWinrEq : W ∘ Sum.inr = fun j => liftWork M₀ U (Sum.inl j) := by
    funext j
    show W (Sum.inr j) = liftWork M₀ U (Sum.inl j)
    rw [copyWA_anc_full hWmem j]
    show (default : Tape (BennettAlph2 Γ Λ ι)).write (Y (Sum.inl j)).1
        = liftWork M₀ U (Sum.inl j)
    have hh : (Y (Sum.inl j)).1 = Sum.inl ((U j).1) := by rw [hYwork j]; rfl
    rw [hh]
    show (default : Tape (BennettAlph2 Γ Λ ι)).write (Sum.inl ((U j).1))
        = Tape.map inlMap (U j)
    rw [cell_lift]
    congr 1
    exact (hU j).symm
  have hUuncompute : liftWork M₀ A ∈
      ktapeSem (phaseU2 M₀) UncompState.RStart (W ∘ Sum.inl) := by
    rw [hWinlY]
    exact (phaseF2_semInverse M₀ q₀).fwd (liftWork M₀ A) Y
      (liftWork_WFblank M₀ A) hY
  rw [bennettB, ktapeSem_seq, Part.mem_bind_iff]
  refine ⟨W, ?_, ?_⟩
  · rw [ktapeSem_seq, Part.mem_bind_iff]
    exact ⟨Uf, hUfmem, hWmem⟩
  · rw [show W = withR (W ∘ Sum.inr) (W ∘ Sum.inl) from (Sum.elim_comp_inl_inr W).symm,
        ktapeSem_liftL, Part.mem_map_iff]
    refine ⟨liftWork M₀ A, hUuncompute, ?_⟩
    rw [hWinrEq]

/-- The Bennett involution machine `D = B ; swap ; B'`. -/
noncomputable def bennettD (M₀ : KMachine Γ Λ ι) (q₀ : Λ) :=
  seq (seq (bennettB M₀) (bankSwap (wAncSwap (ι := ι))) false) (bennettB' M₀)
      (Sum.inl (BennettState2.A1 q₀))

/-- **A5/Option B: `D` simulates `M₀` on head-valued involutive points.**  For
single-cell `A`, `U` with `M₀ A = U` and `M₀ U = A` (the involution), `D` maps the
encoded input `enc A = (liftWork A, blank ancilla)` to `enc U`.  Chains
`bennettB_correct_full` (B) → work↔ancilla swap → `bennettB'_blanks` (B'). -/
theorem bennettD_simulates (M₀ : KMachine Γ Λ ι) (q₀ : Λ) (A U : ι → Tape Γ)
    (hA : ∀ j, IsCell (A j)) (hU : ∀ j, IsCell (U j))
    (hAU : U ∈ ktapeSem M₀ q₀ A) (hUA : A ∈ ktapeSem M₀ q₀ U) :
    withR (fun _ : ι => (default : Tape (BennettAlph2 Γ Λ ι))) (liftWork M₀ U)
      ∈ ktapeSem (bennettD M₀ q₀)
          (Sum.inl (Sum.inl (Sum.inl (Sum.inl (BennettState2.A1 q₀)))))
          (withR (fun _ : ι => (default : Tape (BennettAlph2 Γ Λ ι))) (liftWork M₀ A)) := by
  classical
  have hB := bennettB_correct_full M₀ q₀ A U hU hAU
  set ZB : (ι ⊕ Fin 1) ⊕ ι → Tape (BennettAlph2 Γ Λ ι) :=
    withR (fun j => liftWork M₀ U (Sum.inl j)) (liftWork M₀ A) with hZB
  set VB : (ι ⊕ Fin 1) ⊕ ι → Tape (BennettAlph2 Γ Λ ι) :=
    withR (fun j => liftWork M₀ A (Sum.inl j)) (liftWork M₀ U) with hVB
  -- swap leg: VB = swap(ZB)
  have hswap : VB ∈ ktapeSem (bankSwap (wAncSwap (ι := ι))) false ZB := by
    have hstep : kstep (bankSwap (wAncSwap (ι := ι)) (Γ := BennettAlph2 Γ Λ ι))
        ⟨false, ZB⟩ = some ⟨true, (KStmt.perm (wAncSwap (ι := ι))).apply ZB⟩ := by
      simp [kstep, bankSwap]
    have hhalt : kstep (bankSwap (wAncSwap (ι := ι)) (Γ := BennettAlph2 Γ Λ ι))
        (⟨true, (KStmt.perm (wAncSwap (ι := ι))).apply ZB⟩ :
          KCfg (BennettAlph2 Γ Λ ι) Bool ((ι ⊕ Fin 1) ⊕ ι)) = none := by
      simp [kstep, bankSwap]
    have hVBeq : VB = (KStmt.perm (wAncSwap (ι := ι))).apply ZB := by
      funext i
      show VB i = ZB ((wAncSwap (ι := ι))⁻¹ i)
      rw [wAncSwap_selfInverse]
      rcases i with (j | h) | j <;> rfl
    rw [hVBeq]
    exact (Part.mem_map_iff _).mpr
      ⟨⟨true, (KStmt.perm (wAncSwap (ι := ι))).apply ZB⟩,
        StateTransition.mem_eval.mpr
          ⟨Relation.ReflTransGen.single (Option.mem_def.mpr hstep), hhalt⟩, rfl⟩
  -- B' leg: blanks the (single-cell) ancilla, restores work to liftWork U
  have hBp := bennettB'_blanks M₀ q₀ U A hUA (fun j => liftWork M₀ A (Sum.inl j))
    (fun j => isCell_map (hA j))
  -- assemble D = B ; swap ; B'
  rw [bennettD, ktapeSem_seq, Part.mem_bind_iff]
  refine ⟨VB, ?_, hBp⟩
  rw [ktapeSem_seq, Part.mem_bind_iff]
  exact ⟨ZB, hB, hswap⟩

/-- **Head-valued unconditional symmetrisation (R1, Option B).**  Let `M₀` compute
a partial involution (`hInvol`) and preserve single-cellness (`hcell`: a head-valued
input has a head-valued output).  Then there is a machine `D` over the Bennett
alphabet — with no `KReversible` hypothesis on `M₀` — and an encoding `enc` such
that on every head-valued input `A` with `M₀ A = U`:

* `D` simulates `M₀`: `enc U ∈ ⟦D⟧ (enc A)`; and
* `D` is involutive on the encoded points: also `enc A ∈ ⟦D⟧ (enc U)`.

`D = bennettB ; swap ; bennettB'` is the Bennett conjugation; both conjuncts are
`bennettD_simulates`, the second with `A`, `U` swapped (using the involution
`hInvol` and single-cell preservation `hcell`).  This is the unconditional
analogue of Nakano's symmetrisation for head-valued involutions. -/
theorem nakano_symmetrisation_headvalued (M₀ : KMachine Γ Λ ι) (q₀ : Λ)
    (hInvol : ∀ X Y, Y ∈ ktapeSem M₀ q₀ X → X ∈ ktapeSem M₀ q₀ Y)
    (hcell : ∀ X Y, (∀ j, IsCell (X j)) → Y ∈ ktapeSem M₀ q₀ X → ∀ j, IsCell (Y j)) :
    ∃ (q0' : _) (enc : (ι → Tape Γ) → ((ι ⊕ Fin 1) ⊕ ι → Tape (BennettAlph2 Γ Λ ι))),
      ∀ A U, (∀ j, IsCell (A j)) → U ∈ ktapeSem M₀ q₀ A →
        enc U ∈ ktapeSem (bennettD M₀ q₀) q0' (enc A) ∧
        enc A ∈ ktapeSem (bennettD M₀ q₀) q0' (enc U) := by
  refine ⟨Sum.inl (Sum.inl (Sum.inl (Sum.inl (BennettState2.A1 q₀)))),
    (fun A => withR (fun _ : ι => (default : Tape (BennettAlph2 Γ Λ ι)))
      (liftWork M₀ A)), ?_⟩
  intro A U hA hAU
  have hU : ∀ j, IsCell (U j) := hcell A U hA hAU
  have hUA : A ∈ ktapeSem M₀ q₀ U := hInvol A U hAU
  exact ⟨bennettD_simulates M₀ q₀ A U hA hU hAU hUA,
         bennettD_simulates M₀ q₀ U A hU hA hUA hAU⟩

/-- **`bennettD` computes a partial involution** (in the sense of
`IsPartialInvolutionOn`) on the encoded head-valued involutive points.  This is
the head-valued instance of the symmetrisation conclusion stated against the
paper's central predicate: every output run reads backwards to its input. -/
theorem bennettD_isPartialInvolutionOn (M₀ : KMachine Γ Λ ι) (q₀ : Λ) :
    IsPartialInvolutionOn (bennettD M₀ q₀)
      (Sum.inl (Sum.inl (Sum.inl (Sum.inl (BennettState2.A1 q₀)))))
      (fun X => ∃ A U, (∀ j, IsCell (A j)) ∧ (∀ j, IsCell (U j)) ∧
        U ∈ ktapeSem M₀ q₀ A ∧ A ∈ ktapeSem M₀ q₀ U ∧
        X = withR (fun _ : ι => (default : Tape (BennettAlph2 Γ Λ ι)))
          (liftWork M₀ A)) := by
  rintro X Y ⟨A, U, hA, hU, hAU, hUA, rfl⟩ hY
  have h1 := bennettD_simulates M₀ q₀ A U hA hU hAU hUA
  have h2 := bennettD_simulates M₀ q₀ U A hU hA hUA hAU
  rw [Part.mem_unique hY h1]
  exact h2

/-! ### A concrete non-vacuity witness: the head bit-flip

To show `nakano_symmetrisation_headvalued` is not vacuous we exhibit a genuine
single-cell partial involution it applies to: the machine that negates every
head once and halts.  Over `Bool` the head flip is its own inverse and preserves
single-cellness, so the head-valued symmetrisation applies. -/

/-- Per-cell head flip is an involution on `Bool` tapes. -/
theorem flipCell_invol (T : Tape Bool) :
    (T.write (!T.1)).write (!((T.write (!T.1)).1)) = T := by
  rw [show ((T.write (!T.1)).1) = !T.1 from rfl, Bool.not_not, tape_write_write,
    Tape.write_self]

/-- Per-cell head flip preserves single-cellness. -/
theorem flipCell_isCell {T : Tape Bool} (h : IsCell T) : IsCell (T.write (!T.1)) := by
  have e2 : T.write (!T.1) = (default : Tape Bool).write (!T.1) := by
    conv_lhs => rw [h]
    rw [tape_write_write]; rfl
  show T.write (!T.1) = (default : Tape Bool).write ((T.write (!T.1)).1)
  rw [show ((T.write (!T.1)).1) = !T.1 from rfl, e2]

/-- The head bit-flip machine: one step negates every head, then halts. -/
def flipM0 {ι : Type*} : KMachine Bool Bool ι := fun q b =>
  match q with
  | false => some (true, KStmt.write (fun i => !(b i)))
  | true => none

theorem flipM0_sem {ι : Type*} (X V : ι → Tape Bool) :
    V ∈ ktapeSem flipM0 false X ↔
      V = (KStmt.write (fun i => !(headsV X i))).apply X :=
  singleWrite_ktapeSem flipM0 _ (fun _ => rfl) (fun _ => rfl) X V

theorem flipM0_involution {ι : Type*} (X Y : ι → Tape Bool)
    (hY : Y ∈ ktapeSem flipM0 false X) : X ∈ ktapeSem flipM0 false Y := by
  rw [flipM0_sem] at hY ⊢
  subst hY
  funext i
  exact (flipCell_invol (X i)).symm

theorem flipM0_cellpreserving {ι : Type*} (X Y : ι → Tape Bool)
    (hX : ∀ j, IsCell (X j)) (hY : Y ∈ ktapeSem flipM0 false X) : ∀ j, IsCell (Y j) := by
  rw [flipM0_sem] at hY
  subst hY
  intro j
  exact flipCell_isCell (hX j)

/-- **Non-vacuity.**  The head-valued unconditional symmetrisation applies to the
head bit-flip---a genuine, non-trivial involution---so the theorem is not
vacuous. -/
theorem flipM0_symmetrisable {ι : Type*} :
    ∃ (q0' : _) (enc : (ι → Tape Bool) →
        ((ι ⊕ Fin 1) ⊕ ι → Tape (BennettAlph2 Bool Bool ι))),
      ∀ A U, (∀ j, IsCell (A j)) → U ∈ ktapeSem flipM0 false A →
        enc U ∈ ktapeSem (bennettD flipM0 false) q0' (enc A) ∧
        enc A ∈ ktapeSem (bennettD flipM0 false) q0' (enc U) :=
  nakano_symmetrisation_headvalued flipM0 false flipM0_involution flipM0_cellpreserving

/-! ### The whole family of cellwise involutions

The bit-flip is one instance of a general pattern: any involution `g` on the
alphabet (`g ∘ g = id`) drives a single-cell partial-involution machine, so the
head-valued symmetrisation applies to the \emph{entire} family of cellwise
involutions, over any alphabet. -/

section Cellwise

variable (g : Γ → Γ)

theorem gCell_invol (hg : ∀ x, g (g x) = x) (T : Tape Γ) :
    (T.write (g T.1)).write (g ((T.write (g T.1)).1)) = T := by
  rw [show ((T.write (g T.1)).1) = g T.1 from rfl, hg, tape_write_write, Tape.write_self]

theorem gCell_isCell {T : Tape Γ} (h : IsCell T) : IsCell (T.write (g T.1)) := by
  have e2 : T.write (g T.1) = (default : Tape Γ).write (g T.1) := by
    conv_lhs => rw [h]
    rw [tape_write_write]; rfl
  show T.write (g T.1) = (default : Tape Γ).write ((T.write (g T.1)).1)
  rw [show ((T.write (g T.1)).1) = g T.1 from rfl, e2]

/-- The cellwise-`g` machine: one step applies `g` to every head, then halts. -/
def cellwiseM0 : KMachine Γ Bool ι := fun q b =>
  match q with
  | false => some (true, KStmt.write (fun i => g (b i)))
  | true => none

theorem cellwiseM0_sem (X V : ι → Tape Γ) :
    V ∈ ktapeSem (cellwiseM0 g) false X ↔
      V = (KStmt.write (fun i => g (headsV X i))).apply X :=
  singleWrite_ktapeSem (cellwiseM0 g) _ (fun _ => rfl) (fun _ => rfl) X V

theorem cellwiseM0_involution (hg : ∀ x, g (g x) = x) (X Y : ι → Tape Γ)
    (hY : Y ∈ ktapeSem (cellwiseM0 g) false X) : X ∈ ktapeSem (cellwiseM0 g) false Y := by
  rw [cellwiseM0_sem] at hY ⊢
  subst hY
  funext i
  exact (gCell_invol g hg (X i)).symm

theorem cellwiseM0_cellpreserving (X Y : ι → Tape Γ)
    (hX : ∀ j, IsCell (X j)) (hY : Y ∈ ktapeSem (cellwiseM0 g) false X) :
    ∀ j, IsCell (Y j) := by
  rw [cellwiseM0_sem] at hY
  subst hY
  intro j
  exact gCell_isCell g (hX j)

/-- **The head-valued symmetrisation applies to every cellwise involution.** -/
theorem cellwiseM0_symmetrisable (hg : ∀ x, g (g x) = x) :
    ∃ (q0' : _) (enc : (ι → Tape Γ) →
        ((ι ⊕ Fin 1) ⊕ ι → Tape (BennettAlph2 Γ Bool ι))),
      ∀ A U, (∀ j, IsCell (A j)) → U ∈ ktapeSem (cellwiseM0 g) false A →
        enc U ∈ ktapeSem (bennettD (cellwiseM0 g) false) q0' (enc A) ∧
        enc A ∈ ktapeSem (bennettD (cellwiseM0 g) false) q0' (enc U) :=
  nakano_symmetrisation_headvalued (cellwiseM0 g) false
    (cellwiseM0_involution g hg) (cellwiseM0_cellpreserving g)

end Cellwise

end PeriodicTM
