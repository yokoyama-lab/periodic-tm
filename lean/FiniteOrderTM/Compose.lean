/-
FiniteOrderTM/Compose.lean

Track B, milestone M3: sequential composition of k-tape machines, with the
semantics lemma in Kleisli form:

    ktapeSem (M₁ ; M₂) (inl q₀₁) T  =  (ktapeSem M₁ q₀₁ T).bind (ktapeSem M₂ q₀₂)

Design.  The composite runs on the disjoint state sum `Λ₁ ⊕ Λ₂`.  In the
left copy it follows `M₁`.  Wherever `M₁` has *no* rule (i.e. `M₁` halts),
the composite instead performs a silent hand-over: it writes back the head
vector it just read (a semantic no-op, by `Tape.write_self`) and enters
`M₂`'s start state in the right copy.  In the right copy it follows `M₂`
and halts where `M₂` halts.

Because the hand-over fires exactly where `M₁` halts, and because
`ktapeSem` forgets the final state, the composition lemma needs *no*
hypotheses — no `halt_iff`, no reversibility, nothing.

This is the combinator required by Nakano's symmetrisation (milestone M6):
the symmetrised machine is a composite of a machine, tape-bank moves, and
a flipped machine.
-/
import FiniteOrderTM.MultiTape

namespace PeriodicTM

open Turing

variable {Γ : Type*} [Inhabited Γ]
variable {Λ₁ Λ₂ : Type*}
variable {ι : Type*}

/-! ### The composite machine -/

/-- Sequential composition: run `M₁` in the left copy; where `M₁` halts,
hand over (with a no-op write) to `M₂`'s start state `q₀₂` in the right
copy. -/
def seq (M₁ : KMachine Γ Λ₁ ι) (M₂ : KMachine Γ Λ₂ ι) (q₀₂ : Λ₂) :
    KMachine Γ (Λ₁ ⊕ Λ₂) ι := fun s a =>
  match s with
  | Sum.inl q =>
      match M₁ q a with
      | some (q', st) => some (Sum.inl q', st)
      | none => some (Sum.inr q₀₂, KStmt.write a)
  | Sum.inr q => (M₂ q a).map fun s' => (Sum.inr s'.1, s'.2)

variable {M₁ : KMachine Γ Λ₁ ι} {M₂ : KMachine Γ Λ₂ ι} {q₀₂ : Λ₂}

/-- Writing back the current heads is a no-op. -/
theorem write_heads_apply (T : ι → Tape Γ) :
    (KStmt.write (headsV T)).apply T = T := by
  funext i
  exact Tape.write_self (T i)

/-- A machine halts at `c` iff it has no rule there. -/
theorem kstep_eq_none_iff {Λ : Type*} {M : KMachine Γ Λ ι} {c : KCfg Γ Λ ι} :
    kstep M c = none ↔ M c.q (headsV c.tapes) = none := by
  rcases e : M c.q (headsV c.tapes) with - | s <;> simp [kstep, e]

/-! ### Step lemmas -/

/-- Left copy simulates `M₁`. -/
theorem seq_step_inl {c c' : KCfg Γ Λ₁ ι} (h : kstep M₁ c = some c') :
    kstep (seq M₁ M₂ q₀₂) ⟨Sum.inl c.q, c.tapes⟩
      = some ⟨Sum.inl c'.q, c'.tapes⟩ := by
  obtain ⟨q, T⟩ := c
  rcases e : M₁ q (headsV T) with - | ⟨q', st⟩
  · simp [kstep, e] at h
  · have hc' : (⟨q', st.apply T⟩ : KCfg Γ Λ₁ ι) = c' := by
      simpa [kstep, e] using h
    subst hc'
    simp [kstep, seq, e]

/-- Hand-over: where `M₁` halts, the composite silently enters `M₂`'s start
state, leaving the tapes unchanged. -/
theorem seq_step_handover {q : Λ₁} {T : ι → Tape Γ}
    (h : M₁ q (headsV T) = none) :
    kstep (seq M₁ M₂ q₀₂) ⟨Sum.inl q, T⟩ = some ⟨Sum.inr q₀₂, T⟩ := by
  simp [kstep, seq, h, write_heads_apply]

/-- The right copy is the exact functorial image of `M₂`. -/
theorem kstep_seq_inr (q : Λ₂) (T : ι → Tape Γ) :
    kstep (seq M₁ M₂ q₀₂) ⟨Sum.inr q, T⟩
      = (kstep M₂ ⟨q, T⟩).map fun c => ⟨Sum.inr c.q, c.tapes⟩ := by
  rcases e : M₂ q (headsV T) with - | ⟨q', st⟩ <;> simp [kstep, seq, e]

/-! ### Run lifting -/

theorem seq_reaches_inl {c c' : KCfg Γ Λ₁ ι}
    (h : StateTransition.Reaches (kstep M₁) c c') :
    StateTransition.Reaches (kstep (seq M₁ M₂ q₀₂))
      ⟨Sum.inl c.q, c.tapes⟩ ⟨Sum.inl c'.q, c'.tapes⟩ := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact ih.tail (Option.mem_def.mpr (seq_step_inl (Option.mem_def.mp hstep)))

theorem seq_reaches_inr {c c' : KCfg Γ Λ₂ ι}
    (h : StateTransition.Reaches (kstep M₂) c c') :
    StateTransition.Reaches (kstep (seq M₁ M₂ q₀₂))
      ⟨Sum.inr c.q, c.tapes⟩ ⟨Sum.inr c'.q, c'.tapes⟩ := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      refine ih.tail (Option.mem_def.mpr ?_)
      rw [kstep_seq_inr, Option.mem_def.mp hstep]
      rfl

/-! ### Run decomposition -/

/-- Once in the right copy, a halting run of the composite is exactly a
halting run of `M₂`. -/
theorem seq_eval_inr {q : Λ₂} {T : ι → Tape Γ}
    {c'' : KCfg Γ (Λ₁ ⊕ Λ₂) ι}
    (h : c'' ∈ StateTransition.eval (kstep (seq M₁ M₂ q₀₂)) ⟨Sum.inr q, T⟩) :
    ∃ c₂ : KCfg Γ Λ₂ ι, c'' = ⟨Sum.inr c₂.q, c₂.tapes⟩ ∧
      c₂ ∈ StateTransition.eval (kstep M₂) ⟨q, T⟩ := by
  obtain ⟨hr, hfin⟩ := StateTransition.mem_eval.mp h
  clear h
  have aux : ∀ {a : KCfg Γ (Λ₁ ⊕ Λ₂) ι},
      StateTransition.Reaches (kstep (seq M₁ M₂ q₀₂)) a c'' →
      ∀ q T, a = ⟨Sum.inr q, T⟩ →
      ∃ c₂ : KCfg Γ Λ₂ ι, c'' = ⟨Sum.inr c₂.q, c₂.tapes⟩ ∧
        c₂ ∈ StateTransition.eval (kstep M₂) ⟨q, T⟩ := by
    intro a hr'
    induction hr' using Relation.ReflTransGen.head_induction_on with
    | refl =>
        rintro q T rfl
        have hM₂ : kstep M₂ (⟨q, T⟩ : KCfg Γ Λ₂ ι) = none := by
          have hfin' := hfin
          rw [kstep_seq_inr] at hfin'
          rcases e : kstep M₂ (⟨q, T⟩ : KCfg Γ Λ₂ ι) with - | c₂
          · rfl
          · rw [e] at hfin'; simp at hfin'
        exact ⟨⟨q, T⟩, rfl,
          StateTransition.mem_eval.mpr ⟨Relation.ReflTransGen.refl, hM₂⟩⟩
    | head h' hrest ih =>
        rintro q T rfl
        have hs := Option.mem_def.mp h'
        rw [kstep_seq_inr] at hs
        rcases e : kstep M₂ (⟨q, T⟩ : KCfg Γ Λ₂ ι) with - | c₂
        · rw [e] at hs; simp at hs
        · rw [e] at hs
          simp only [Option.map_some, Option.some.injEq] at hs
          obtain ⟨c₂', hc'', hev⟩ := ih c₂.q c₂.tapes hs.symm
          refine ⟨c₂', hc'', ?_⟩
          obtain ⟨hr₂, hf₂⟩ := StateTransition.mem_eval.mp hev
          exact StateTransition.mem_eval.mpr
            ⟨Relation.ReflTransGen.head (Option.mem_def.mpr e) hr₂, hf₂⟩
  exact aux hr q T rfl

/-- In the left copy, a halting run of the composite splits into a halting
run of `M₁` followed by the hand-over. -/
theorem seq_eval_inl {q : Λ₁} {T : ι → Tape Γ}
    {c'' : KCfg Γ (Λ₁ ⊕ Λ₂) ι}
    (hfin : kstep (seq M₁ M₂ q₀₂) c'' = none)
    (hr : StateTransition.Reaches (kstep (seq M₁ M₂ q₀₂)) ⟨Sum.inl q, T⟩ c'') :
    ∃ c₁ : KCfg Γ Λ₁ ι, c₁ ∈ StateTransition.eval (kstep M₁) ⟨q, T⟩ ∧
      StateTransition.Reaches (kstep (seq M₁ M₂ q₀₂))
        ⟨Sum.inr q₀₂, c₁.tapes⟩ c'' := by
  have aux : ∀ {a : KCfg Γ (Λ₁ ⊕ Λ₂) ι},
      StateTransition.Reaches (kstep (seq M₁ M₂ q₀₂)) a c'' →
      ∀ q T, a = ⟨Sum.inl q, T⟩ →
      ∃ c₁ : KCfg Γ Λ₁ ι, c₁ ∈ StateTransition.eval (kstep M₁) ⟨q, T⟩ ∧
        StateTransition.Reaches (kstep (seq M₁ M₂ q₀₂))
          ⟨Sum.inr q₀₂, c₁.tapes⟩ c'' := by
    intro a hr'
    induction hr' using Relation.ReflTransGen.head_induction_on with
    | refl =>
        rintro q T rfl
        -- the left copy never halts: contradiction with `hfin`
        exfalso
        rcases e : M₁ q (headsV T) with - | ⟨q', st⟩ <;>
          simp [kstep, seq, e] at hfin
    | head h' hrest ih =>
        rintro q T rfl
        have hs := Option.mem_def.mp h'
        rcases e : M₁ q (headsV T) with - | ⟨q', st⟩
        · -- hand-over: M₁ halts here
          have hsh : kstep (seq M₁ M₂ q₀₂) ⟨Sum.inl q, T⟩
              = some ⟨Sum.inr q₀₂, T⟩ := seq_step_handover e
          rw [hsh] at hs
          obtain rfl := Option.some.inj hs.symm
          refine ⟨⟨q, T⟩, ?_, hrest⟩
          refine StateTransition.mem_eval.mpr ⟨Relation.ReflTransGen.refl, ?_⟩
          simp [kstep, e]
        · -- ordinary `M₁` step
          have hstep₁ : kstep M₁ (⟨q, T⟩ : KCfg Γ Λ₁ ι)
              = some ⟨q', st.apply T⟩ := by
            simp [kstep, e]
          have hseq := seq_step_inl (M₂ := M₂) (q₀₂ := q₀₂) hstep₁
          rw [hseq] at hs
          obtain rfl := Option.some.inj hs.symm
          obtain ⟨c₁, hev₁, hr₂⟩ := ih q' (st.apply T) rfl
          refine ⟨c₁, ?_, hr₂⟩
          obtain ⟨hr₁, hf₁⟩ := StateTransition.mem_eval.mp hev₁
          exact StateTransition.mem_eval.mpr
            ⟨Relation.ReflTransGen.head (Option.mem_def.mpr hstep₁) hr₁, hf₁⟩
  exact aux hr q T rfl

/-! ### The composition theorem -/

/-- **Sequential composition, Kleisli form** (milestone M3).  The tape
semantics of the composite is the `Part.bind` of the components'.  No side
hypotheses: the hand-over fires exactly where `M₁` halts, and `ktapeSem`
forgets final states. -/
theorem ktapeSem_seq (M₁ : KMachine Γ Λ₁ ι) (M₂ : KMachine Γ Λ₂ ι)
    (q₀₁ : Λ₁) (q₀₂ : Λ₂) (T : ι → Tape Γ) :
    ktapeSem (seq M₁ M₂ q₀₂) (Sum.inl q₀₁) T
      = (ktapeSem M₁ q₀₁ T).bind (ktapeSem M₂ q₀₂) := by
  ext T''
  rw [Part.mem_bind_iff]
  constructor
  · intro hT''
    obtain ⟨c'', hc'', rfl⟩ := (Part.mem_map_iff _).mp hT''
    obtain ⟨hr, hfin⟩ := StateTransition.mem_eval.mp hc''
    obtain ⟨c₁, hev₁, hr₂⟩ := seq_eval_inl hfin hr
    obtain ⟨c₂, rfl, hev₂⟩ :=
      seq_eval_inr (StateTransition.mem_eval.mpr ⟨hr₂, hfin⟩)
    exact ⟨c₁.tapes, (Part.mem_map_iff _).mpr ⟨c₁, hev₁, rfl⟩,
      (Part.mem_map_iff _).mpr ⟨c₂, hev₂, rfl⟩⟩
  · rintro ⟨T', hT', hT''⟩
    obtain ⟨c₁, hev₁, rfl⟩ := (Part.mem_map_iff _).mp hT'
    obtain ⟨c₂, hev₂, rfl⟩ := (Part.mem_map_iff _).mp hT''
    obtain ⟨hr₁, hf₁⟩ := StateTransition.mem_eval.mp hev₁
    obtain ⟨hr₂, hf₂⟩ := StateTransition.mem_eval.mp hev₂
    refine (Part.mem_map_iff _).mpr
      ⟨⟨Sum.inr c₂.q, c₂.tapes⟩, StateTransition.mem_eval.mpr ⟨?_, ?_⟩, rfl⟩
    · have l1 := seq_reaches_inl (M₂ := M₂) (q₀₂ := q₀₂) hr₁
      have l2 : kstep (seq M₁ M₂ q₀₂) ⟨Sum.inl c₁.q, c₁.tapes⟩
          = some ⟨Sum.inr q₀₂, c₁.tapes⟩ :=
        seq_step_handover (kstep_eq_none_iff.mp hf₁)
      have l3 := seq_reaches_inr (M₁ := M₁) (q₀₂ := q₀₂) hr₂
      exact l1.trans (Relation.ReflTransGen.head (Option.mem_def.mpr l2) l3)
    · rw [show (⟨Sum.inr c₂.q, c₂.tapes⟩ : KCfg Γ (Λ₁ ⊕ Λ₂) ι)
          = ⟨Sum.inr c₂.q, c₂.tapes⟩ from rfl, kstep_seq_inr]
      have : kstep M₂ (⟨c₂.q, c₂.tapes⟩ : KCfg Γ Λ₂ ι) = none := hf₂
      rw [this]
      rfl

end PeriodicTM
