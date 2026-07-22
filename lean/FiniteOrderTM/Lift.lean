/-
FiniteOrderTM/Lift.lean

Track B, milestone M4: tape-bank lifting.  A machine over tape index `ι`
lifts to a machine over `ι ⊕ κ` that works on the left bank and leaves the
right bank untouched.

Because the tape index is an arbitrary type (the model was generalised from
`Fin k` for exactly this purpose), the lift is plain `Sum` plumbing — no
`Fin` arithmetic:

* a `write b⃗` rule writes `b⃗` on the left bank and writes back the heads it
  has just read on the right bank (a no-op there, by `Tape.write_self`);
* a `move d⃗` rule moves nothing on the right bank;
* a `perm π` rule becomes `perm (π ⊕ refl)`.

The semantics lemma (`ktapeSem_liftL`) says the lift computes exactly the
original function on the left bank, with the right bank as a frozen
parameter:

    ktapeSem (liftL M) q₀ U
      = (ktapeSem M q₀ (U ∘ inl)).map (fun T => Sum.elim T (U ∘ inr)).

As with sequential composition, there are no side hypotheses.
-/
import FiniteOrderTM.Compose

namespace PeriodicTM

open Turing

variable {Γ : Type*} [Inhabited Γ]
variable {Λ : Type*}
variable {ι κ : Type*}

/-! ### The lifted machine -/

/-- Lift a statement over `ι` to one over `ι ⊕ κ`, given the head vector
`a` currently read (used to make the `write` a no-op on the right bank). -/
def KStmt.inflate (a : ι ⊕ κ → Γ) : KStmt Γ ι → KStmt Γ (ι ⊕ κ)
  | KStmt.write b => KStmt.write (Sum.elim b (a ∘ Sum.inr))
  | KStmt.move d => KStmt.move (Sum.elim d fun _ => none)
  | KStmt.perm π => KStmt.perm (Equiv.sumCongr π (Equiv.refl κ))

/-- Lift a machine over `ι` to one over `ι ⊕ κ`: read only the left-bank
heads, act only on the left bank. -/
def liftL (M : KMachine Γ Λ ι) : KMachine Γ Λ (ι ⊕ κ) := fun q a =>
  (M q (a ∘ Sum.inl)).map fun s => (s.1, s.2.inflate a)

/-- Recombine a left bank with a frozen right bank. -/
def withR (S : κ → Tape Γ) (T : ι → Tape Γ) : ι ⊕ κ → Tape Γ :=
  Sum.elim T S

@[simp] theorem withR_inl (S : κ → Tape Γ) (T : ι → Tape Γ) :
    withR S T ∘ Sum.inl = T := rfl

@[simp] theorem withR_inr (S : κ → Tape Γ) (T : ι → Tape Γ) :
    withR S T ∘ Sum.inr = S := rfl

/-! ### Statement-level correctness -/

theorem inflate_apply (st : KStmt Γ ι) (T : ι → Tape Γ) (S : κ → Tape Γ) :
    (st.inflate (headsV (withR S T))).apply (withR S T)
      = withR S (st.apply T) := by
  rcases st with b | d | π
  · -- write: left bank writes `b`, right bank writes back its own heads
    funext j
    rcases j with i | r
    · rfl
    · exact Tape.write_self (S r)
  · -- move: right bank does not move
    funext j
    rcases j with i | r
    · rfl
    · rfl
  · -- perm: `π ⊕ refl` permutes the left bank only
    funext j
    rcases j with i | r
    · show (withR S T) ((Equiv.sumCongr π (Equiv.refl κ))⁻¹ (Sum.inl i)) = _
      simp [withR, KStmt.apply]
    · show (withR S T) ((Equiv.sumCongr π (Equiv.refl κ))⁻¹ (Sum.inr r)) = _
      simp [withR, KStmt.apply]

/-! ### Step-level correspondence -/

/-- The lifted machine is the functorial image of `M` with the right bank
frozen. -/
theorem kstep_liftL (M : KMachine Γ Λ ι) (q : Λ) (T : ι → Tape Γ)
    (S : κ → Tape Γ) :
    kstep (liftL M (κ := κ)) ⟨q, withR S T⟩
      = (kstep M ⟨q, T⟩).map fun c => ⟨c.q, withR S c.tapes⟩ := by
  have hheads : headsV (withR S T) ∘ Sum.inl = headsV T := rfl
  rcases e : M q (headsV T) with - | ⟨q', st⟩
  · simp [kstep, liftL, hheads, e]
  · simp only [kstep, liftL, hheads, e, Option.map_some]
    exact congrArg some (congrArg _ (inflate_apply st T S))

/-! ### Run-level correspondence -/

theorem reaches_liftL {M : KMachine Γ Λ ι} {c c' : KCfg Γ Λ ι}
    (S : κ → Tape Γ)
    (h : StateTransition.Reaches (kstep M) c c') :
    StateTransition.Reaches (kstep (liftL M (κ := κ)))
      ⟨c.q, withR S c.tapes⟩ ⟨c'.q, withR S c'.tapes⟩ := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      refine ih.tail (Option.mem_def.mpr ?_)
      rw [kstep_liftL, Option.mem_def.mp hstep]
      rfl

/-! ### The lifting theorem -/

/-- **Tape-bank lifting** (milestone M4): the lifted machine computes the
original function on the left bank and leaves the right bank untouched.
No side hypotheses. -/
theorem ktapeSem_liftL (M : KMachine Γ Λ ι) (q₀ : Λ)
    (T : ι → Tape Γ) (S : κ → Tape Γ) :
    ktapeSem (liftL M (κ := κ)) q₀ (withR S T)
      = (ktapeSem M q₀ T).map (withR S) := by
  ext U''
  constructor
  · intro hU''
    obtain ⟨c'', hc'', rfl⟩ := (Part.mem_map_iff _).mp hU''
    obtain ⟨hr, hfin⟩ := StateTransition.mem_eval.mp hc''
    -- decompose the lifted run: the right bank is frozen along it
    have aux : ∀ {a : KCfg Γ Λ (ι ⊕ κ)},
        StateTransition.Reaches (kstep (liftL M (κ := κ))) a c'' →
        ∀ q T, a = ⟨q, withR S T⟩ →
        ∃ c₁ : KCfg Γ Λ ι, c'' = ⟨c₁.q, withR S c₁.tapes⟩ ∧
          c₁ ∈ StateTransition.eval (kstep M) ⟨q, T⟩ := by
      intro a hr'
      induction hr' using Relation.ReflTransGen.head_induction_on with
      | refl =>
          rintro q T rfl
          have hM : kstep M (⟨q, T⟩ : KCfg Γ Λ ι) = none := by
            have hfin' := hfin
            rw [kstep_liftL] at hfin'
            rcases e : kstep M (⟨q, T⟩ : KCfg Γ Λ ι) with - | c₁
            · rfl
            · rw [e] at hfin'; simp at hfin'
          exact ⟨⟨q, T⟩, rfl,
            StateTransition.mem_eval.mpr ⟨Relation.ReflTransGen.refl, hM⟩⟩
      | head h' hrest ih =>
          rintro q T rfl
          have hs := Option.mem_def.mp h'
          rw [kstep_liftL] at hs
          rcases e : kstep M (⟨q, T⟩ : KCfg Γ Λ ι) with - | c₁
          · rw [e] at hs; simp at hs
          · rw [e] at hs
            simp only [Option.map_some, Option.some.injEq] at hs
            obtain ⟨c₁', hc'', hev⟩ := ih c₁.q c₁.tapes hs.symm
            refine ⟨c₁', hc'', ?_⟩
            obtain ⟨hr₁, hf₁⟩ := StateTransition.mem_eval.mp hev
            exact StateTransition.mem_eval.mpr
              ⟨Relation.ReflTransGen.head (Option.mem_def.mpr e) hr₁, hf₁⟩
    obtain ⟨c₁, rfl, hev⟩ := aux hr q₀ T rfl
    exact (Part.mem_map_iff _).mpr
      ⟨c₁.tapes, (Part.mem_map_iff _).mpr ⟨c₁, hev, rfl⟩, rfl⟩
  · intro hU''
    obtain ⟨T', hT', rfl⟩ := (Part.mem_map_iff _).mp hU''
    obtain ⟨c₁, hev₁, rfl⟩ := (Part.mem_map_iff _).mp hT'
    obtain ⟨hr₁, hf₁⟩ := StateTransition.mem_eval.mp hev₁
    refine (Part.mem_map_iff _).mpr
      ⟨⟨c₁.q, withR S c₁.tapes⟩, StateTransition.mem_eval.mpr ⟨?_, ?_⟩, rfl⟩
    · exact reaches_liftL S hr₁
    · rw [kstep_liftL]
      have hf₁' : kstep M (⟨c₁.q, c₁.tapes⟩ : KCfg Γ Λ ι) = none := hf₁
      rw [hf₁']
      rfl

/-- **Membership form of the lifting theorem.**  Any output of the lifted
machine freezes the right bank (`U ∘ inr = X ∘ inr`) and runs `M` on the left
bank (`U ∘ inl ∈ ⟦M⟧ (X ∘ inl)`).  Used to discharge the frozen-bank hand-over
obligations of the F;C;U wrapper. -/
theorem ktapeSem_liftL_mem (M : KMachine Γ Λ ι) (q₀ : Λ)
    {X U : ι ⊕ κ → Tape Γ} (h : U ∈ ktapeSem (liftL M (κ := κ)) q₀ X) :
    U ∘ Sum.inr = X ∘ Sum.inr ∧ U ∘ Sum.inl ∈ ktapeSem M q₀ (X ∘ Sum.inl) := by
  rw [show X = withR (X ∘ Sum.inr) (X ∘ Sum.inl) from (Sum.elim_comp_inl_inr X).symm,
      ktapeSem_liftL, Part.mem_map_iff] at h
  obtain ⟨UL, hUL, rfl⟩ := h
  exact ⟨rfl, hUL⟩

end PeriodicTM
