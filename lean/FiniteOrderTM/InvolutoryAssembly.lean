/-
FiniteOrderTM/InvolutoryAssembly.lean

Roadmap step 4 (assembly): the StdOutput/standard-intermediate argument
turning the `tapeSem` equation of `conjugationClosure_tapeSem` /
`conjugationClosure_of_reversibilisation` into the `stringSem` equation
demanded by `StringConjugationClosure` (InvolutoryString.lean).

Contents:

* **Abstract standard-output discipline** for partial tape functions
  (`TapeFnStd`, `strOf`): `StdOutput M q₀` is exactly
  `TapeFnStd (tapeSem M q₀)` and `stringSem M q₀` is exactly
  `strOf (tapeSem M q₀)`, so composition lemmas can be proved once, at the
  level of partial tape functions, and reused for arbitrary machine
  composites.

* **StdOutput transport under Kleisli composition**: `TapeFnStd.bind` /
  `TapeFnStd.bind₂` (a composite of standard-output tape functions has
  standard output) and `TapeFnStd.strOf_bind` / `TapeFnStd.strOf_bind₂`
  (the string semantics of the composite is the Kleisli composition of the
  legs' string semantics; only the *earlier* legs' standardness is
  consumed, because `readTape` counts symbols and `readTape_length` pins
  all intermediate lengths to `s.length`).  Machine-level packaging:
  `stdOutput_stringSem_of_tapeSem_bind` (two legs, the `seq` shape) and
  `stdOutput_stringSem_of_tapeSem_bind₂` (three legs, the conjugation
  shape).

* **The step-4 assembly theorem**
  `stringConjugationClosure_of_reversibilisation`: for `R` with a
  `Reversibilisation` witness `K` (InvolutoryBennett.lean), `M`
  syntactically involutory, and `StdOutput` for the three legs
  (`ofK K`, `M`, `ofK (flipM K σK)`), there is a syntactically involutory
  `TM0` machine `D` with **standard output**, computing at `stringSem`
  level the conjugation `⟦flipM K⟧ ∘ ⟦M⟧ ∘ ⟦R⟧` — and hence (soundness)
  `StringInvolutory D d₀`.  `stringConjugationClosure_instance` restates
  it in the exact existential shape of `StringConjugationClosure`, given
  that some machine `R'` computes the flip leg's string function.

* **The concrete writeK/writeHead family**: `liftInvol f` lifts an
  alphabet involution to a `Unit`-bank head-vector involution;
  `ofK (writeK (liftInvol f)) = writeHead f` on the nose;
  `reversibilisation_writeHead` gives the `Reversibilisation` witness; the
  flip leg is computed in closed form
  (`tapeSem_ofK_flipM_writeK`: it is again `T ↦ T.write (f T.1)`), giving
  its `StdOutput` and `stringSem`.  The milestone
  `stringConjugationClosure_applyHead` then discharges the full
  string-level conjugation closure for this family: every string map
  `applyHead f ∘ applyHead g ∘ applyHead f` (`f`, `g` blank-fixing
  alphabet involutions) — an involution by `applyHead_conj_involutive` —
  is computed *totally* by a syntactically involutory machine.  One-cell
  completeness closed under conjugation by the one-cell reversible maps.
-/
import FiniteOrderTM.InvolutoryBennett

namespace PeriodicTM

open Turing Turing.TM0

variable {Γ : Type*} [Inhabited Γ] {Λ : Type*} [Inhabited Λ]

/-! ### Abstract standard-output discipline for partial tape functions -/

/-- Standard-output discipline for a partial tape function: on a standard
input tape the output tape is standard (left blank, head at position 0).
`StdOutput M q₀` is definitionally `TapeFnStd (tapeSem M q₀)`. -/
def TapeFnStd (F : Tape Γ → Part (Tape Γ)) : Prop :=
  ∀ (s : List Γ) (T' : Tape Γ),
    T' ∈ F (Tape.mk₁ s) → T' = Tape.mk₁ (readTape s.length T')

/-- The string function induced by a partial tape function under the
standard-configuration I/O convention.  `stringSem M q₀` is definitionally
`strOf (tapeSem M q₀)`. -/
noncomputable def strOf (F : Tape Γ → Part (Tape Γ)) (s : List Γ) :
    Part (List Γ) :=
  (F (Tape.mk₁ s)).map (readTape s.length)

/-- `StdOutput` is the machine instance of `TapeFnStd`. -/
theorem StdOutput.std {M : Machine Γ Λ} {q₀ : Λ} (h : StdOutput M q₀) :
    TapeFnStd (tapeSem M q₀) :=
  h.left_blank

/-- `stringSem` is the machine instance of `strOf`. -/
theorem stringSem_eq_strOf (M : Machine Γ Λ) (q₀ : Λ) (s : List Γ) :
    stringSem M q₀ s = strOf (tapeSem M q₀) s := rfl

/-- Reading back a string of the right length from its standard tape. -/
theorem readTape_mk₁_of_length {n : ℕ} {v : List Γ} (h : v.length = n) :
    readTape n (Tape.mk₁ v) = v := by
  rw [← h, readTape_mk₁]

/-! ### StdOutput transport under Kleisli composition -/

omit [Inhabited Λ] in
/-- **StdOutput of a two-leg composite**: the Kleisli composition of two
standard-output tape functions has standard output.  The intermediate tape
is standard by `hF`, its string has length `s.length` by `readTape_length`,
and `hG` then standardises the final tape. -/
theorem TapeFnStd.bind {F G : Tape Γ → Part (Tape Γ)}
    (hF : TapeFnStd F) (hG : TapeFnStd G) :
    TapeFnStd (fun T => (F T).bind G) := by
  intro s T'' hT''
  rw [Part.mem_bind_iff] at hT''
  obtain ⟨T', hT', hG'⟩ := hT''
  rw [hF s T' hT'] at hG'
  have h2 := hG _ T'' hG'
  rwa [readTape_length] at h2

omit [Inhabited Λ] in
/-- **StdOutput of a three-leg composite** (the conjugation shape). -/
theorem TapeFnStd.bind₂ {F G H : Tape Γ → Part (Tape Γ)}
    (hF : TapeFnStd F) (hG : TapeFnStd G) (hH : TapeFnStd H) :
    TapeFnStd (fun T => (F T).bind fun u => (G u).bind H) := by
  intro s T₃ hT₃
  simp only [Part.mem_bind_iff] at hT₃
  obtain ⟨T₁, h1, T₂, h2, h3⟩ := hT₃
  rw [hF s T₁ h1] at h2
  rw [hG _ T₂ h2] at h3
  have h4 := hH _ T₃ h3
  rwa [readTape_length, readTape_length] at h4

omit [Inhabited Λ] in
/-- **String semantics of a two-leg composite**: the string function of the
Kleisli composition is the Kleisli composition of the string functions.
Only the *first* leg's standardness is needed: the final read counts
`s.length` symbols, and `readTape_length` pins the intermediate string's
length to `s.length` regardless of the second leg's geometry. -/
theorem TapeFnStd.strOf_bind {F G : Tape Γ → Part (Tape Γ)}
    (hF : TapeFnStd F) (s : List Γ) :
    strOf (fun T => (F T).bind G) s = (strOf F s).bind (strOf G) := by
  ext t
  simp only [strOf, Part.mem_map_iff, Part.mem_bind_iff]
  constructor
  · rintro ⟨T₂, ⟨T₁, h1, h2⟩, rfl⟩
    rw [hF s T₁ h1] at h2
    refine ⟨readTape s.length T₁, ⟨T₁, h1, rfl⟩, T₂, h2, ?_⟩
    rw [readTape_length]
  · rintro ⟨u, ⟨T₁, h1, rfl⟩, T₂, h2, rfl⟩
    refine ⟨T₂, ⟨T₁, h1, ?_⟩, ?_⟩
    · rw [hF s T₁ h1]; exact h2
    · rw [readTape_length]

omit [Inhabited Λ] in
/-- **String semantics of a three-leg composite** (the conjugation shape);
consumes standardness of the first two legs only. -/
theorem TapeFnStd.strOf_bind₂ {F G H : Tape Γ → Part (Tape Γ)}
    (hF : TapeFnStd F) (hG : TapeFnStd G) (s : List Γ) :
    strOf (fun T => (F T).bind fun u => (G u).bind H) s
      = (strOf F s).bind fun u => (strOf G u).bind (strOf H) := by
  ext t
  simp only [strOf, Part.mem_map_iff, Part.mem_bind_iff]
  constructor
  · rintro ⟨T₃, ⟨T₁, h1, T₂, h2, h3⟩, rfl⟩
    rw [hF s T₁ h1] at h2
    have h2' := h2
    rw [hG _ T₂ h2] at h3
    refine ⟨readTape s.length T₁, ⟨T₁, h1, rfl⟩,
      readTape (readTape s.length T₁).length T₂, ⟨T₂, h2', rfl⟩,
      T₃, h3, ?_⟩
    rw [readTape_length, readTape_length]
  · rintro ⟨u, ⟨T₁, h1, rfl⟩, v, ⟨T₂, h2, rfl⟩, T₃, h3, rfl⟩
    refine ⟨T₃, ⟨T₁, h1, T₂, ?_, ?_⟩, ?_⟩
    · rw [hF s T₁ h1]; exact h2
    · rw [hG _ T₂ h2]; exact h3
    · rw [readTape_length, readTape_length]

/-! ### Machine-level packaging -/

/-- `StdOutput` transports along semantic equality of machines. -/
theorem StdOutput.congr {Λ' : Type*} [Inhabited Λ']
    {M : Machine Γ Λ} {N : Machine Γ Λ'} {q₀ : Λ} {p₀ : Λ'}
    (hMN : ∀ T, tapeSem M q₀ T = tapeSem N p₀ T) (hN : StdOutput N p₀) :
    StdOutput M q₀ :=
  ⟨fun s T' hT' => hN.left_blank s T' (hMN (Tape.mk₁ s) ▸ hT')⟩

/-- `stringSem` transports along semantic equality of machines. -/
theorem stringSem_congr {Λ' : Type*} [Inhabited Λ']
    {M : Machine Γ Λ} {N : Machine Γ Λ'} {q₀ : Λ} {p₀ : Λ'}
    (hMN : ∀ T, tapeSem M q₀ T = tapeSem N p₀ T) (s : List Γ) :
    stringSem M q₀ s = stringSem N p₀ s := by
  simp only [stringSem, hMN]

/-- **Two-leg machine transport** (the `seq` shape): if `D` computes the
Kleisli composition of `A` then `B` at tape level and both legs have
standard output, then `D` has standard output and its string semantics is
the Kleisli composition of the legs' string semantics. -/
theorem stdOutput_stringSem_of_tapeSem_bind
    {ΛD ΛA ΛB : Type*} [Inhabited ΛD] [Inhabited ΛA] [Inhabited ΛB]
    {D : Machine Γ ΛD} {A : Machine Γ ΛA} {B : Machine Γ ΛB}
    {d₀ : ΛD} {a₀ : ΛA} {b₀ : ΛB}
    (hD : ∀ T, tapeSem D d₀ T = (tapeSem A a₀ T).bind (tapeSem B b₀))
    (hA : StdOutput A a₀) (hB : StdOutput B b₀) :
    StdOutput D d₀ ∧
    ∀ s, stringSem D d₀ s = (stringSem A a₀ s).bind (stringSem B b₀) := by
  refine ⟨⟨fun s T' hT' => TapeFnStd.bind hA.std hB.std s T' ?_⟩, fun s => ?_⟩
  · show T' ∈ (tapeSem A a₀ (Tape.mk₁ s)).bind (tapeSem B b₀)
    rw [← hD]; exact hT'
  calc stringSem D d₀ s
      = strOf (fun T => (tapeSem A a₀ T).bind (tapeSem B b₀)) s := by
        simp only [stringSem, strOf, hD]
    _ = (strOf (tapeSem A a₀) s).bind (strOf (tapeSem B b₀)) :=
        TapeFnStd.strOf_bind hA.std s
    _ = (stringSem A a₀ s).bind (stringSem B b₀) := rfl

/-- **Three-leg machine transport** (the conjugation shape). -/
theorem stdOutput_stringSem_of_tapeSem_bind₂
    {ΛD ΛA ΛB ΛC : Type*}
    [Inhabited ΛD] [Inhabited ΛA] [Inhabited ΛB] [Inhabited ΛC]
    {D : Machine Γ ΛD} {A : Machine Γ ΛA} {B : Machine Γ ΛB}
    {C : Machine Γ ΛC} {d₀ : ΛD} {a₀ : ΛA} {b₀ : ΛB} {c₀ : ΛC}
    (hD : ∀ T, tapeSem D d₀ T
      = (tapeSem A a₀ T).bind fun u => (tapeSem B b₀ u).bind (tapeSem C c₀))
    (hA : StdOutput A a₀) (hB : StdOutput B b₀) (hC : StdOutput C c₀) :
    StdOutput D d₀ ∧
    ∀ s, stringSem D d₀ s
      = (stringSem A a₀ s).bind fun u =>
          (stringSem B b₀ u).bind (stringSem C c₀) := by
  refine ⟨⟨fun s T' hT' => TapeFnStd.bind₂ hA.std hB.std hC.std s T' ?_⟩,
    fun s => ?_⟩
  · show T' ∈ (tapeSem A a₀ (Tape.mk₁ s)).bind fun u =>
      (tapeSem B b₀ u).bind (tapeSem C c₀)
    rw [← hD]; exact hT'
  calc stringSem D d₀ s
      = strOf (fun T => (tapeSem A a₀ T).bind fun u =>
          (tapeSem B b₀ u).bind (tapeSem C c₀)) s := by
        simp only [stringSem, strOf, hD]
    _ = (strOf (tapeSem A a₀) s).bind fun u =>
          (strOf (tapeSem B b₀) u).bind (strOf (tapeSem C c₀)) :=
        TapeFnStd.strOf_bind₂ hA.std hB.std s
    _ = (stringSem A a₀ s).bind fun u =>
          (stringSem B b₀ u).bind (stringSem C c₀) := rfl

/-! ### The step-4 assembly theorem -/

/-- **String-level conjugation closure for reversibilisable conjugators**
(the step-4 assembly): given a `Reversibilisation` witness `K` for `R`, a
syntactically involutory `M`, and `StdOutput` for the three legs, there is
a syntactically involutory machine `D` *with standard output* whose string
semantics is the conjugation `⟦flipM K⟧ ∘ ⟦M⟧ ∘ ⟦R⟧` — and consequently
(`SyntacticallyInvolutory.stringInvolutory`) `D` computes a partial string
involution.  This turns the `tapeSem` equation of
`conjugationClosure_of_reversibilisation` into the `stringSem` equation of
`StringConjugationClosure` via `stdOutput_stringSem_of_tapeSem_bind₂`. -/
theorem stringConjugationClosure_of_reversibilisation
    (Γ ΛR ΛK ΛM : Type) [Inhabited Γ] [Inhabited ΛR] [Inhabited ΛK]
    [Inhabited ΛM]
    (R : Machine Γ ΛR) (r₀ : ΛR)
    (K : KMachine Γ ΛK Unit) (σK : ΛK → ΛK) (k₀ kf : ΛK)
    (M : Machine Γ ΛM) (σM : ΛM → ΛM) (q0M qfM : ΛM)
    (hK : Reversibilisation R r₀ K σK k₀ kf)
    (hM : Involutory M σM q0M qfM)
    (hSO_R : StdOutput (ofK K) k₀)
    (hSO_M : StdOutput M q0M)
    (hSO_R' : StdOutput (ofK (flipM K σK)) (σK kf)) :
    ∃ (Λ' : Type) (_ : Inhabited Λ') (D : Machine Γ Λ') (d₀ df : Λ'),
      SyntacticallyInvolutory D d₀ df ∧ StdOutput D d₀ ∧
      StringInvolutory D d₀ ∧
      ∀ s, stringSem D d₀ s =
        (stringSem R r₀ s).bind fun u =>
          (stringSem M q0M u).bind
            (stringSem (ofK (flipM K σK)) (σK kf)) := by
  obtain ⟨-, Λ', inst, D, d₀, df, hsyn, hsem⟩ :=
    conjugationClosure_of_reversibilisation Γ ΛR ΛK ΛM R r₀ K σK k₀ kf
      M σM q0M qfM hK hM
  letI := inst
  have hsem' : ∀ T, tapeSem D d₀ T
      = (tapeSem (ofK K) k₀ T).bind fun u =>
          (tapeSem M q0M u).bind (tapeSem (ofK (flipM K σK)) (σK kf)) :=
    fun T => by simpa only [← tapeSem_ofK] using hsem T
  obtain ⟨hSO_D, hstr⟩ :=
    stdOutput_stringSem_of_tapeSem_bind₂ hsem' hSO_R hSO_M hSO_R'
  refine ⟨Λ', inst, D, d₀, df, hsyn, hSO_D,
    hsyn.stringInvolutory hSO_D, fun s => ?_⟩
  rw [hstr s, hK.sem s]

/-- The assembly theorem in the exact existential shape of
`StringConjugationClosure`: if additionally some machine `R'` computes the
flip leg's string function (the semantic inverse of `⟦R⟧`), the conjugation
`⟦R'⟧ ∘ ⟦M⟧ ∘ ⟦R⟧` is computed at `stringSem` level by a syntactically
involutory machine. -/
theorem stringConjugationClosure_instance
    (Γ ΛR ΛK ΛM ΛR' : Type) [Inhabited Γ] [Inhabited ΛR] [Inhabited ΛK]
    [Inhabited ΛM] [Inhabited ΛR']
    (R : Machine Γ ΛR) (r₀ : ΛR)
    (K : KMachine Γ ΛK Unit) (σK : ΛK → ΛK) (k₀ kf : ΛK)
    (M : Machine Γ ΛM) (σM : ΛM → ΛM) (q0M qfM : ΛM)
    (R' : Machine Γ ΛR') (r₀' : ΛR')
    (hK : Reversibilisation R r₀ K σK k₀ kf)
    (hM : Involutory M σM q0M qfM)
    (hSO_R : StdOutput (ofK K) k₀)
    (hSO_M : StdOutput M q0M)
    (hSO_R' : StdOutput (ofK (flipM K σK)) (σK kf))
    (hR' : ∀ t, stringSem (ofK (flipM K σK)) (σK kf) t
      = stringSem R' r₀' t) :
    ∃ (Λ' : Type) (_ : Inhabited Λ') (D : Machine Γ Λ') (d₀ df : Λ'),
      SyntacticallyInvolutory D d₀ df ∧
      ∀ s, stringSem D d₀ s =
        (stringSem R r₀ s).bind fun u =>
          (stringSem M q0M u).bind (stringSem R' r₀') := by
  obtain ⟨Λ', inst, D, d₀, df, hsyn, -, -, hstr⟩ :=
    stringConjugationClosure_of_reversibilisation Γ ΛR ΛK ΛM R r₀ K σK
      k₀ kf M σM q0M qfM hK hM hSO_R hSO_M hSO_R'
  exact ⟨Λ', inst, D, d₀, df, hsyn,
    fun s => by rw [hstr s, funext hR']⟩

/-! ### The concrete family: alphabet involutions as conjugators -/

/-- Lift an alphabet map to a `Unit`-bank head-vector map. -/
def liftInvol (f : Γ → Γ) : (Unit → Γ) → (Unit → Γ) := fun b _ => f (b ())

omit [Inhabited Γ] in
theorem liftInvol_invol {f : Γ → Γ} (hf : ∀ a, f (f a) = a) :
    ∀ x, liftInvol (Γ := Γ) f (liftInvol f x) = x := fun x =>
  funext fun u => by cases u; exact hf (x ())

omit [Inhabited Γ] in
/-- The collapsed `Unit`-bank writer is the one-cell writer, on the nose. -/
theorem ofK_writeK_liftInvol (f : Γ → Γ) :
    ofK (writeK (liftInvol f)) = writeHead f := by
  funext q a
  cases q <;> rfl

/-- The one-cell writer `writeHead f` (an involution `f` on the alphabet)
is reversibilised by its own `Unit`-bank embedding `writeK (liftInvol f)`:
the concrete `Reversibilisation` witness for the writeHead family. -/
theorem reversibilisation_writeHead (f : Γ → Γ) (hf : ∀ a, f (f a) = a) :
    Reversibilisation (writeHead f) false (writeK (liftInvol f))
      not false true :=
  ofK_writeK_liftInvol f ▸
    Reversibilisation.ofK_self Bool.not_not
      (writeK_reversible (liftInvol_invol hf))
      (writeK_halt_iff (liftInvol f)) (writeK_entry (liftInvol_invol hf))

/-- **Closed form of the flip leg**: for an alphabet involution `f`, the
collapsed flip of the `Unit`-bank writer computes exactly the one-cell
write again — `T ↦ T.write (f T.1)` (the inverse of an involution is
itself). -/
theorem tapeSem_ofK_flipM_writeK (f : Γ → Γ) (hf : ∀ a, f (f a) = a)
    (T : Tape Γ) :
    tapeSem (ofK (flipM (writeK (liftInvol f)) not)) (not true) T
      = Part.some (T.write (f T.1)) := by
  have hrev := writeK_reversible (Γ := Γ) (ι := Unit) (liftInvol_invol hf)
  have hhalt := writeK_halt_iff (Γ := Γ) (ι := Unit) (liftInvol f)
  have hent := writeK_entry (Γ := Γ) (ι := Unit) (liftInvol_invol hf)
  ext T'
  rw [tapeSem_ofK, Part.mem_map_iff, Part.mem_some_iff]
  constructor
  · rintro ⟨U, hU, rfl⟩
    have hmem : (fun _ : Unit => T)
        ∈ ktapeSem (writeK (liftInvol f)) false U :=
      (flipM_tapeSem_inverse Bool.not_not hrev hhalt hent).mpr hU
    rw [ktapeSem_writeK, Part.mem_some_iff] at hmem
    have hc : T = (U ()).write (f ((U ()).1)) := congrFun hmem ()
    rw [hc, show ((U ()).write (f ((U ()).1))).1 = f ((U ()).1) from rfl,
      hf, tape_write_write, Tape.write_self]
  · rintro rfl
    refine ⟨fun _ => T.write (f T.1), ?_, rfl⟩
    apply (flipM_tapeSem_inverse Bool.not_not hrev hhalt hent).mp
    rw [ktapeSem_writeK, Part.mem_some_iff]
    funext u
    cases u
    show T = (T.write (f T.1)).write (f ((T.write (f T.1)).1))
    rw [show ((T.write (f T.1)).1) = f T.1 from rfl, hf, tape_write_write,
      Tape.write_self]

/-- The flip leg has standard output for a blank-fixing involution `f`
(its semantics coincides with `writeHead f`, whose `StdOutput` is
`writeHead_stdOutput`). -/
theorem stdOutput_ofK_flipM_writeK (f : Γ → Γ) (hf : ∀ a, f (f a) = a)
    (hfdef : f default = default) :
    StdOutput (ofK (flipM (writeK (liftInvol f)) not)) (not true) := by
  have hMN : ∀ T, tapeSem (ofK (flipM (writeK (liftInvol f)) not))
      (not true) T = tapeSem (writeHead f) false T := fun T => by
    rw [tapeSem_ofK_flipM_writeK f hf, tapeSem_writeHead]
  exact StdOutput.congr hMN (writeHead_stdOutput f hfdef)

/-- String semantics of the flip leg: `applyHead f`, totally. -/
theorem stringSem_ofK_flipM_writeK (f : Γ → Γ) (hf : ∀ a, f (f a) = a)
    (s : List Γ) :
    stringSem (ofK (flipM (writeK (liftInvol f)) not)) (not true) s
      = Part.some (applyHead f s) := by
  have hMN : ∀ T, tapeSem (ofK (flipM (writeK (liftInvol f)) not))
      (not true) T = tapeSem (writeHead f) false T := fun T => by
    rw [tapeSem_ofK_flipM_writeK f hf, tapeSem_writeHead]
  rw [stringSem_congr hMN s, stringSem_writeHead]

omit [Inhabited Γ] in
/-- The conjugated head map is a string involution. -/
theorem applyHead_conj_involutive (f g : Γ → Γ)
    (hf : ∀ a, f (f a) = a) (hg : ∀ a, g (g a) = a) (s : List Γ) :
    applyHead f (applyHead g (applyHead f
      (applyHead f (applyHead g (applyHead f s))))) = s := by
  rw [applyHead_involutive f hf, applyHead_involutive g hg,
    applyHead_involutive f hf]

/-- **Milestone: string-level conjugation closure for the writeHead
family.**  For blank-fixing alphabet involutions `f` (the conjugator) and
`g` (the conjugated involution), the string involution
`applyHead f ∘ applyHead g ∘ applyHead f` — the conjugation of the
one-cell involution `⟦writeHead g⟧` by the syntactically reversible
one-cell map `⟦writeHead f⟧` (its own string inverse) — is computed
*totally* by a syntactically involutory machine that moreover has standard
output and computes a partial string involution.  This closes the one-cell
completeness kernel (`completenessGoal_oneCell_string`) under conjugation
by the one-cell reversible string maps: a genuine instance of
`StringConjugationClosure` beyond the bare kernel. -/
theorem stringConjugationClosure_applyHead (Γ : Type) [Inhabited Γ]
    (f g : Γ → Γ)
    (hf : ∀ a, f (f a) = a) (hfdef : f default = default)
    (hg : ∀ a, g (g a) = a) (hgdef : g default = default) :
    ∃ (Λ' : Type) (_ : Inhabited Λ') (D : Machine Γ Λ') (d₀ df : Λ'),
      SyntacticallyInvolutory D d₀ df ∧ StringInvolutory D d₀ ∧
      ∀ s, stringSem D d₀ s
        = Part.some (applyHead f (applyHead g (applyHead f s))) := by
  obtain ⟨Λ', inst, D, d₀, df, hsyn, -, hstrinv, hstr⟩ :=
    stringConjugationClosure_of_reversibilisation Γ Bool Bool Bool
      (writeHead f) false (writeK (liftInvol f)) not false true
      (writeHead g) not false true
      (reversibilisation_writeHead f hf) (involutory_writeHead g hg)
      ((ofK_writeK_liftInvol f).symm ▸ writeHead_stdOutput f hfdef)
      (writeHead_stdOutput g hgdef)
      (stdOutput_ofK_flipM_writeK f hf hfdef)
  haveI := inst
  refine ⟨Λ', inst, D, d₀, df, hsyn, hstrinv, fun s => ?_⟩
  rw [hstr s, stringSem_writeHead, Part.bind_some, stringSem_writeHead,
    Part.bind_some, stringSem_ofK_flipM_writeK f hf]

/-!
### Roadmap delta (step 4: assembly)

**Done here:**
* The `StdOutput`/standard-intermediate transport, factored through the
  abstract discipline `TapeFnStd`/`strOf`: composites of standard-output
  legs have standard output (`TapeFnStd.bind`, `TapeFnStd.bind₂`) and
  their string semantics is the Kleisli composition of the legs' string
  semantics (`TapeFnStd.strOf_bind`, `TapeFnStd.strOf_bind₂` — notably,
  only the *earlier* legs' standardness is consumed, since `readTape`
  reads a fixed count of symbols).  Machine packagings
  `stdOutput_stringSem_of_tapeSem_bind`(`₂`).
* **The assembly theorem** `stringConjugationClosure_of_reversibilisation`:
  `Reversibilisation` witness + syntactic involutivity of `M` + `StdOutput`
  of the three legs ⟹ a syntactically involutory `D` with `StdOutput`,
  `StringInvolutory`, and the `stringSem` conjugation equation; restated in
  the exact `StringConjugationClosure` shape by
  `stringConjugationClosure_instance`.  This discharges item 2 of the
  step-4 list in `InvolutoryBennett.lean` (turning the `tapeSem` equation
  into the `stringSem` equation) *given* per-leg `StdOutput`.
* **A fully discharged nontrivial instance**
  (`stringConjugationClosure_applyHead`): for the writeHead family (blank-
  fixing alphabet involutions conjugated by one-cell reversible writes),
  every side condition is verified — `Reversibilisation` via
  `reversibilisation_writeHead`, `StdOutput` of all legs, closed-form flip
  leg (`tapeSem_ofK_flipM_writeK`) — yielding total computation of
  `applyHead f ∘ applyHead g ∘ applyHead f` by a syntactically involutory
  machine.  One-cell completeness is therefore *closed under conjugation*
  by the one-cell reversible string maps.

**Remaining gap to full `StringConjugationClosure` /
`StringCompletenessGoal`:**
1. `ReversibilisationGoal` (InvolutoryBennett.lean): produce a
   `Reversibilisation` witness from a merely *semantically* invertible
   `R` — the Bennett history-logging simulator.  With such a witness, the
   assembly theorem here applies verbatim.
2. `StdOutput` for the legs of a *general* reversibilised conjugator: the
   history construction must return heads to position 0 and leave the
   left tape blank (Nakano's symmetrisation bookkeeping).  For machines in
   the writeHead/writeK family this is proved here; in general it is a
   property of the not-yet-built history simulator, not of the transport.
3. The 2k-tape encoding (`Lift`/`Reindex` + hidden-bank encoding) needed
   to state and discharge `StringCompletenessGoal` itself, where `stringSem`
   agreement replaces `tapeSem` equality and the ancilla banks are hidden
   by the encoding.
-/

end PeriodicTM
