/-
# Semantic reversibility: decoupling function-level symmetrisation from `KReversible`

`conj_partial_involution` (Symmetrise.lean) conjugates an involutory machine
`M` by a *syntactically* reversible machine `R`, building the inverse leg as
`flipM R σR`.  But its proof uses only ONE fact about that leg: that the leg
computes the inverse partial function (the local `invR`).  This file isolates
that fact as `SemInverse`, so the function-level symmetrisation no longer
mentions `KReversible` at all---any machine `R'` whose tape semantics inverts
`R`'s will do.

Why this is the bridge for milestone M8.  The Bennett descriptor simulator is
*not* `KReversible` (`phaseF2_not_backdet`), yet its semantics is injective
(`phaseF2_ktapeSem_inj`).  `conj_partial_involution_sem` pins down exactly what
is still required to reach `nakano_symmetrisation_unconditional`: an inverse
*machine* `R'` for the reversibiliser (the uncompute leg), not the syntactic
discipline.  `KReversible` stays *sufficient* (`KReversible.semInverse` yields
`flipM R σR` as such an `R'`), so the original theorem is a corollary
(`conj_partial_involution_of_KReversible`).

DOMAIN RESTRICTION (R1 Stage 1b).  The Python prototype
`proto/bennett_uncompute.py` showed that an *unrestricted* inverse relation
(`∀ X Y, Y ∈ ⟦R⟧ X ↔ X ∈ ⟦R'⟧ Y`) is FALSE for the Bennett uncompute machine:
on non-reachable `Y` (work-cell history junk, a misplaced history head, blank
gaps) the reverse machine halts with a spurious `X` for which `⟦R⟧ X ≠ Y`.  The
forward leg (`fwd`: every `R`-output reverses) *does* hold unconditionally, but
the backward leg (`bwd`) holds only on a domain `Dom` of well-formed/reachable
outputs.  `SemInverse` therefore carries an explicit `Dom` predicate and gates
`bwd` by it; `conj_partial_involution_sem` discharges the domain obligation from
the fact that the conjugation's middle leg `M` maps `R`-outputs into `Dom`.

Scope.  The decoupling is for the *partial-involution* (function-level) result,
which is what the function-level completeness goal needs.  The *syntactic*
`conj_KInvolutory` genuinely uses `flipM`'s rule-level flip structure and is not
decoupled here (nor need it be: the Bennett simulator is not a syntactic
`KInvolutory` object).
-/
import FiniteOrderTM.Symmetrise

namespace PeriodicTM

open Turing

variable {Γ : Type*} [Inhabited Γ] {ι : Type*}
variable {ΛR ΛR' ΛM : Type*}

/-- `R'` semantically inverts `R` on the domain `Dom`.

* `fwd` (unconditional): every `R`-output run reverses -- if `Y ∈ ⟦R⟧ X` then
  `X ∈ ⟦R'⟧ Y`.
* `bwd` (gated by `Dom`): on inputs `Y` in `Dom`, every `R'`-run is a genuine
  reversal -- if `Dom Y` and `X ∈ ⟦R'⟧ Y` then `Y ∈ ⟦R⟧ X`.

For a `KReversible` machine both legs hold with `Dom = ⊤` (the flip is a total
inverse).  For the Bennett uncompute machine `Dom` is the set of reachable/
well-formed outputs; `bwd` genuinely fails off `Dom`. -/
structure SemInverse (R : KMachine Γ ΛR ι) (R' : KMachine Γ ΛR' ι)
    (q0R : ΛR) (q0R' : ΛR') (DomIn DomOut : (ι → Tape Γ) → Prop) : Prop where
  fwd : ∀ X Y, DomIn X → Y ∈ ktapeSem R q0R X → X ∈ ktapeSem R' q0R' Y
  bwd : ∀ X Y, DomOut Y → X ∈ ktapeSem R' q0R' Y → Y ∈ ktapeSem R q0R X

/-- **Bridge (syntactic ⟹ semantic).**  A `KReversible` machine has a semantic
inverse on the *full* domain: its own flip `flipM R σR`.  This is
`flipM_tapeSem_inverse` repackaged as a `SemInverse` witness with `Dom = ⊤`. -/
theorem KReversible.semInverse {R : KMachine Γ ΛR ι} {σR : ΛR → ΛR}
    {q0R qfR : ΛR} (hσR : ∀ q, σR (σR q) = q) (hRrev : KReversible R)
    (hRhalt : ∀ q a, R q a = none ↔ q = qfR)
    (hRent : ∀ q b, (∃ v, Demand R q b v) ↔ q ≠ q0R) :
    SemInverse R (flipM R σR) q0R (σR qfR) (fun _ => True) (fun _ => True) where
  fwd := fun X Y _ h =>
    (flipM_tapeSem_inverse hσR hRrev hRhalt hRent (T := X) (T' := Y)).mp h
  bwd := fun X Y _ h =>
    (flipM_tapeSem_inverse hσR hRrev hRhalt hRent (T := X) (T' := Y)).mpr h

/-- A semantic inverse forces `R`'s tape semantics to be injective (the converse
relation is a partial function because `ktapeSem` is).  Uses only `fwd`, so it
holds for any domain.  This ties `SemInverse` back to the injectivity
established for the Bennett simulator (`phaseF2_ktapeSem_inj`): having an inverse
*machine* is strictly more than being injective. -/
theorem SemInverse.injective {R : KMachine Γ ΛR ι} {R' : KMachine Γ ΛR' ι}
    {q0R : ΛR} {q0R' : ΛR'} {DomIn DomOut : (ι → Tape Γ) → Prop}
    (h : SemInverse R R' q0R q0R' DomIn DomOut)
    {X₁ X₂ Y : ι → Tape Γ} (hd1 : DomIn X₁) (hd2 : DomIn X₂)
    (h₁ : Y ∈ ktapeSem R q0R X₁) (h₂ : Y ∈ ktapeSem R q0R X₂) : X₁ = X₂ :=
  Part.mem_unique (h.fwd X₁ Y hd1 h₁) (h.fwd X₂ Y hd2 h₂)

/-- **Semantic conjugation (Lemma 4.4, decoupled).**  If `M` is involutory and
`R'` semantically inverts `R` on a domain `Dom` that `M` maps `R`-outputs into,
the conjugate `seq (seq R M) R'` computes a partial involution.  No reversibility
*discipline* is assumed---only the (domain-restricted) semantic inverse relation.

The domain obligation `hdom` is exactly what the prototype showed is needed: the
backward leg of `SemInverse` is applied only to the conjugation's middle value
`V ∈ ⟦M⟧ U` with `U` an `R`-output, so `Dom V` must follow from that. -/
theorem conj_partial_involution_sem
    {R : KMachine Γ ΛR ι} {R' : KMachine Γ ΛR' ι} {M : KMachine Γ ΛM ι}
    {σM : ΛM → ΛM} {q0R : ΛR} {q0R' : ΛR'} {q0M qfM : ΛM}
    {DomIn DomOut : (ι → Tape Γ) → Prop}
    (hM : KInvolutory M σM q0M qfM)
    (hinv : SemInverse R R' q0R q0R' DomIn DomOut)
    (hdom : ∀ U V, (∃ T, DomIn T ∧ U ∈ ktapeSem R q0R T) →
            V ∈ ktapeSem M q0M U → DomOut V)
    {T T' : ι → Tape Γ} (hT : DomIn T)
    (h : T' ∈ ktapeSem (seq (seq R M q0M) R' q0R') (Sum.inl (Sum.inl q0R)) T) :
    T ∈ ktapeSem (seq (seq R M q0M) R' q0R') (Sum.inl (Sum.inl q0R)) T' := by
  rw [ktapeSem_seq, ktapeSem_seq] at h ⊢
  rw [Part.mem_bind_iff] at h
  obtain ⟨V, hV, hT'⟩ := h
  rw [Part.mem_bind_iff] at hV
  obtain ⟨U, hU, hVU⟩ := hV
  -- hU : U ∈ ⟦R⟧ T ; hVU : V ∈ ⟦M⟧ U ; hT' : T' ∈ ⟦R'⟧ V
  have hVT' : V ∈ ktapeSem R q0R T' := hinv.bwd T' V (hdom U V ⟨T, hT, hU⟩ hVU) hT'
  have hUV : U ∈ ktapeSem M q0M V := hM.ktapeSem_involutive hVU
  have hTU : T ∈ ktapeSem R' q0R' U := hinv.fwd T U hT hU
  rw [Part.mem_bind_iff]
  exact ⟨U, Part.mem_bind_iff.mpr ⟨V, hVT', hUV⟩, hTU⟩

/-- The original `conj_partial_involution` (with `R' = flipM R σR`) recovered as
a corollary of the decoupled theorem through the `KReversible ⟹ SemInverse`
bridge.  The domain is `⊤`, so `hdom` is trivial.  Confirms the abstraction is
faithful: the semantic hypothesis is a genuine weakening of `KReversible`. -/
theorem conj_partial_involution_of_KReversible
    {R : KMachine Γ ΛR ι} {M : KMachine Γ ΛM ι}
    {σR : ΛR → ΛR} {σM : ΛM → ΛM} {q0R qfR : ΛR} {q0M qfM : ΛM}
    (hM : KInvolutory M σM q0M qfM)
    (hσR : ∀ q, σR (σR q) = q) (hRrev : KReversible R)
    (hRhalt : ∀ q a, R q a = none ↔ q = qfR)
    (hRent : ∀ q b, (∃ v, Demand R q b v) ↔ q ≠ q0R)
    {T T' : ι → Tape Γ}
    (h : T' ∈ ktapeSem (seq (seq R M q0M) (flipM R σR) (σR qfR))
        (Sum.inl (Sum.inl q0R)) T) :
    T ∈ ktapeSem (seq (seq R M q0M) (flipM R σR) (σR qfR))
        (Sum.inl (Sum.inl q0R)) T' :=
  conj_partial_involution_sem hM
    (KReversible.semInverse hσR hRrev hRhalt hRent)
    (fun _ _ _ _ => trivial) trivial h

/-! ### Compositionality of `SemInverse` (for the F;C;U wrapper)

The Bennett forward/copy/uncompute machine is `seq (seq F C) U`; its semantic
inverse is the reverse composition.  `SemInverse.seq` shows the inverse relation
composes through `seq`, given the domains line up across the hand-over.  This is
the reusable abstraction for the reversibility of the F;C;U wrapper. -/

variable {Λ₁ Λ₁' Λ₂ Λ₂' : Type*}

/-- **`SemInverse` composes through `seq`.**  If `R₁'`/`R₂'` semantically invert
`R₁`/`R₂`, and the domains line up across the hand-over (`R₁` maps `DomIn₁`
outputs into `DomIn₂`, and `R₂'` maps `DomOut₂` outputs into `DomOut₁`), then
`seq R₂' R₁'` semantically inverts `seq R₁ R₂`. -/
theorem SemInverse.seq
    {R₁ : KMachine Γ Λ₁ ι} {R₁' : KMachine Γ Λ₁' ι}
    {R₂ : KMachine Γ Λ₂ ι} {R₂' : KMachine Γ Λ₂' ι}
    {q0₁ : Λ₁} {q0₁' : Λ₁'} {q0₂ : Λ₂} {q0₂' : Λ₂'}
    {DomIn₁ DomOut₁ DomIn₂ DomOut₂ : (ι → Tape Γ) → Prop}
    (h₁ : SemInverse R₁ R₁' q0₁ q0₁' DomIn₁ DomOut₁)
    (h₂ : SemInverse R₂ R₂' q0₂ q0₂' DomIn₂ DomOut₂)
    (hcompat : ∀ X U, DomIn₁ X → U ∈ ktapeSem R₁ q0₁ X → DomIn₂ U)
    (hcompat' : ∀ Y V, DomOut₂ Y → V ∈ ktapeSem R₂' q0₂' Y → DomOut₁ V) :
    SemInverse (seq R₁ R₂ q0₂) (seq R₂' R₁' q0₁')
      (Sum.inl q0₁) (Sum.inl q0₂') DomIn₁ DomOut₂ where
  fwd := by
    intro X Y hX hY
    rw [ktapeSem_seq, Part.mem_bind_iff] at hY
    obtain ⟨U, hU, hY⟩ := hY
    rw [ktapeSem_seq, Part.mem_bind_iff]
    exact ⟨U, h₂.fwd U Y (hcompat X U hX hU) hY, h₁.fwd X U hX hU⟩
  bwd := by
    intro X Y hY hX
    rw [ktapeSem_seq, Part.mem_bind_iff] at hX
    obtain ⟨U, hU, hX⟩ := hX
    rw [ktapeSem_seq, Part.mem_bind_iff]
    exact ⟨U, h₁.bwd X U (hcompat' Y U hY hU) hX, h₂.bwd U Y hY hU⟩

/-- **Forward leg of `seq` composition.**  The forward implication alone needs
only the two forward legs and the *input-side* hand-over (`hcompat`); the hard
backward hand-over (`hcompat'` in `SemInverse.seq`) is not required.  This is what
lets the F;C;U wrapper get its backward direction for free via `Part.mem_unique`
on an image domain (mirroring `phaseF2_semInverse`), sidestepping the
ancilla-correctness coupling that a full `SemInverse.seq` would force. -/
theorem SemInverse.fwd_seq
    {R₁ : KMachine Γ Λ₁ ι} {R₁' : KMachine Γ Λ₁' ι}
    {R₂ : KMachine Γ Λ₂ ι} {R₂' : KMachine Γ Λ₂' ι}
    {q0₁ : Λ₁} {q0₁' : Λ₁'} {q0₂ : Λ₂} {q0₂' : Λ₂'}
    {DomIn₁ DomIn₂ : (ι → Tape Γ) → Prop}
    (h₁fwd : ∀ X U, DomIn₁ X → U ∈ ktapeSem R₁ q0₁ X → X ∈ ktapeSem R₁' q0₁' U)
    (h₂fwd : ∀ U Y, DomIn₂ U → Y ∈ ktapeSem R₂ q0₂ U → U ∈ ktapeSem R₂' q0₂' Y)
    (hcompat : ∀ X U, DomIn₁ X → U ∈ ktapeSem R₁ q0₁ X → DomIn₂ U)
    (X Y : ι → Tape Γ) (hX : DomIn₁ X)
    (hY : Y ∈ ktapeSem (PeriodicTM.seq R₁ R₂ q0₂) (Sum.inl q0₁) X) :
    X ∈ ktapeSem (PeriodicTM.seq R₂' R₁' q0₁') (Sum.inl q0₂') Y := by
  rw [ktapeSem_seq, Part.mem_bind_iff] at hY
  obtain ⟨U, hU, hY⟩ := hY
  rw [ktapeSem_seq, Part.mem_bind_iff]
  exact ⟨U, h₂fwd U Y (hcompat X U hX hU) hY, h₁fwd X U hX hU⟩

/-- **`SemInverse` is preserved by `liftL`.**  Lifting both legs onto a larger
bank index `ι ⊕ κ` keeps the semantic-inverse relation: the right bank `κ` is a
frozen parameter, so the lifted domains constrain only the left bank
(`fun U => DomIn (U ∘ Sum.inl)`).  Together with `SemInverse.seq` this assembles
the reversibility of the Bennett F;C;U wrapper, whose legs live on different
sub-banks of a common index. -/
theorem SemInverse.liftL {κ : Type*}
    {R : KMachine Γ Λ₁ ι} {R' : KMachine Γ Λ₁' ι}
    {q0 : Λ₁} {q0' : Λ₁'} {DomIn DomOut : (ι → Tape Γ) → Prop}
    (h : SemInverse R R' q0 q0' DomIn DomOut) :
    SemInverse (liftL R (κ := κ)) (liftL R' (κ := κ)) q0 q0'
      (fun U => DomIn (U ∘ Sum.inl)) (fun U => DomOut (U ∘ Sum.inl)) where
  fwd := by
    intro X Y hX hY
    rw [show X = withR (X ∘ Sum.inr) (X ∘ Sum.inl) from (Sum.elim_comp_inl_inr X).symm,
        ktapeSem_liftL, Part.mem_map_iff] at hY
    obtain ⟨YL, hYL, rfl⟩ := hY
    rw [ktapeSem_liftL, Part.mem_map_iff]
    exact ⟨X ∘ Sum.inl, h.fwd _ _ hX hYL, Sum.elim_comp_inl_inr X⟩
  bwd := by
    intro X Y hY hX
    rw [show Y = withR (Y ∘ Sum.inr) (Y ∘ Sum.inl) from (Sum.elim_comp_inl_inr Y).symm,
        ktapeSem_liftL, Part.mem_map_iff] at hX
    obtain ⟨XL, hXL, rfl⟩ := hX
    rw [ktapeSem_liftL, Part.mem_map_iff]
    exact ⟨Y ∘ Sum.inl, h.bwd _ _ hY hXL, Sum.elim_comp_inl_inr Y⟩

/-- **`SemInverse` is symmetric.**  Swapping the two machines (and their start
states and domains) gives a semantic inverse the other way: `fwd`/`bwd` are
mirror images.  This is exactly what makes `phaseU2` invert `phaseF2` *and*
`phaseF2` invert `phaseU2` (the F-leg and U-leg of the Bennett wrapper). -/
theorem SemInverse.symm {R : KMachine Γ ΛR ι} {R' : KMachine Γ ΛR' ι}
    {q0R : ΛR} {q0R' : ΛR'} {DomIn DomOut : (ι → Tape Γ) → Prop}
    (h : SemInverse R R' q0R q0R' DomIn DomOut) :
    SemInverse R' R q0R' q0R DomOut DomIn where
  fwd := fun X Y hX hY => h.bwd Y X hX hY
  bwd := fun X Y hY hX => h.fwd Y X hY hX

/-- **Domains are antitone.**  Shrinking the input/output domains preserves
`SemInverse` (the legs only get *more* hypotheses).  Used to strengthen a leg's
domain before a `seq` hand-over -- e.g. adding `AncBlank` to the forward leg's
input domain so the copy leg's precondition is met. -/
theorem SemInverse.mono {R : KMachine Γ ΛR ι} {R' : KMachine Γ ΛR' ι}
    {q0R : ΛR} {q0R' : ΛR'}
    {DomIn DomOut DomIn' DomOut' : (ι → Tape Γ) → Prop}
    (h : SemInverse R R' q0R q0R' DomIn DomOut)
    (hin : ∀ X, DomIn' X → DomIn X) (hout : ∀ Y, DomOut' Y → DomOut Y) :
    SemInverse R R' q0R q0R' DomIn' DomOut' where
  fwd := fun X Y hX hY => h.fwd X Y (hin X hX) hY
  bwd := fun X Y hY hX => h.bwd X Y (hout Y hY) hX

end PeriodicTM
