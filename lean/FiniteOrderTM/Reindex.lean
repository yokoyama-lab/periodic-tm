/-
FiniteOrderTM/Reindex.lean

Bank-index reindexing: transport a machine along a bank-index equivalence
`e : ι ≃ ι'`.  This generalises `liftL` (which embeds `ι ↪ ι ⊕ κ`, freezing the
extra banks) to an arbitrary *bijective* renaming of banks, so a machine proven
correct/reversible on one bank layout can be reused on another.  Composed with
`liftL` it drops a small machine (e.g. the full-string copy on `Unit ⊕ Unit`)
into a larger frozen layout.

`ktapeSem_renameBank` is the semantics lemma (mirror of `ktapeSem_liftL`):

    ktapeSem (renameBank e M) q₀ T' = (ktapeSem M q₀ (T' ∘ e)).map (· ∘ e.symm).

`SemInverse.renameBank` transports the semantic inverse relation.
-/
import FiniteOrderTM.SemReversible

namespace PeriodicTM

open Turing

variable {Γ : Type*} [Inhabited Γ] {Λ : Type*} {ι ι' : Type*}

/-- Rename the banks of a statement along `e : ι ≃ ι'`. -/
def KStmt.rename (e : ι ≃ ι') : KStmt Γ ι → KStmt Γ ι'
  | KStmt.write b => KStmt.write (fun i' => b (e.symm i'))
  | KStmt.move d => KStmt.move (fun i' => d (e.symm i'))
  | KStmt.perm π => KStmt.perm (e.permCongr π)

/-- Rename the banks of a machine along `e : ι ≃ ι'`. -/
def renameBank (e : ι ≃ ι') (M : KMachine Γ Λ ι) : KMachine Γ Λ ι' := fun q a' =>
  (M q (fun i => a' (e i))).map fun s => (s.1, s.2.rename e)

theorem rename_apply (e : ι ≃ ι') (st : KStmt Γ ι) (T' : ι' → Tape Γ) :
    (st.rename e).apply T' = fun i' => (st.apply (fun i => T' (e i))) (e.symm i') := by
  rcases st with b | d | π
  · funext i'
    show (T' i').write (b (e.symm i')) = (T' (e (e.symm i'))).write (b (e.symm i'))
    rw [Equiv.apply_symm_apply]
  · funext i'
    simp only [KStmt.rename, KStmt.apply, Equiv.apply_symm_apply]
  · funext i'
    show T' ((e.permCongr π)⁻¹ i') = T' (e (π⁻¹ (e.symm i')))
    rw [← Equiv.permCongr_apply]; rfl

theorem kstep_renameBank (e : ι ≃ ι') (M : KMachine Γ Λ ι) (q : Λ) (T' : ι' → Tape Γ) :
    kstep (renameBank e M) ⟨q, T'⟩
      = (kstep M ⟨q, fun i => T' (e i)⟩).map fun c => ⟨c.q, fun i' => c.tapes (e.symm i')⟩ := by
  have hheads : headsV (fun i => T' (e i)) = fun i => headsV T' (e i) := rfl
  rcases h : M q (fun i => headsV T' (e i)) with - | ⟨q', st⟩
  · simp [kstep, renameBank, hheads, h]
  · simp only [kstep, renameBank, hheads, h, Option.map_some]
    refine congrArg some (congrArg _ ?_)
    exact rename_apply e st T'

theorem reaches_renameBank (e : ι ≃ ι') {M : KMachine Γ Λ ι} {c c' : KCfg Γ Λ ι}
    (h : StateTransition.Reaches (kstep M) c c') :
    StateTransition.Reaches (kstep (renameBank e M))
      ⟨c.q, fun i' => c.tapes (e.symm i')⟩ ⟨c'.q, fun i' => c'.tapes (e.symm i')⟩ := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      refine ih.tail (Option.mem_def.mpr ?_)
      rw [kstep_renameBank]
      simp only [Equiv.symm_apply_apply]
      rw [Option.mem_def.mp hstep]
      rfl

theorem ktapeSem_renameBank (e : ι ≃ ι') (M : KMachine Γ Λ ι) (q₀ : Λ) (T' : ι' → Tape Γ) :
    ktapeSem (renameBank e M) q₀ T' = (ktapeSem M q₀ (fun i => T' (e i))).map (fun U i' => U (e.symm i')) := by
  ext U''
  constructor
  · intro hU''
    obtain ⟨c'', hc'', rfl⟩ := (Part.mem_map_iff _).mp hU''
    obtain ⟨hr, hfin⟩ := StateTransition.mem_eval.mp hc''
    have aux : ∀ {a : KCfg Γ Λ ι'},
        StateTransition.Reaches (kstep (renameBank e M)) a c'' →
        ∀ q T, a = ⟨q, fun i' => T (e.symm i')⟩ →
        ∃ c₁ : KCfg Γ Λ ι, c'' = ⟨c₁.q, fun i' => c₁.tapes (e.symm i')⟩ ∧
          c₁ ∈ StateTransition.eval (kstep M) ⟨q, T⟩ := by
      intro a hr'
      induction hr' using Relation.ReflTransGen.head_induction_on with
      | refl =>
          rintro q T rfl
          have hM : kstep M (⟨q, T⟩ : KCfg Γ Λ ι) = none := by
            have hfin' := hfin
            rw [kstep_renameBank] at hfin'
            rcases e2 : kstep M (⟨q, fun i => (fun i' => T (e.symm i')) (e i)⟩ : KCfg Γ Λ ι) with - | c₁
            · rw [show (fun i => (fun i' => T (e.symm i')) (e i)) = T from
                funext fun i => by simp only [Equiv.symm_apply_apply]] at e2
              exact e2
            · rw [e2] at hfin'; simp at hfin'
          exact ⟨⟨q, T⟩, rfl,
            StateTransition.mem_eval.mpr ⟨Relation.ReflTransGen.refl, hM⟩⟩
      | head h' hrest ih =>
          rintro q T rfl
          have hs := Option.mem_def.mp h'
          rw [kstep_renameBank] at hs
          rw [show (fun i => (fun i' => T (e.symm i')) (e i)) = T from
            funext fun i => by simp only [Equiv.symm_apply_apply]] at hs
          rcases e2 : kstep M (⟨q, T⟩ : KCfg Γ Λ ι) with - | c₁
          · rw [e2] at hs; simp at hs
          · rw [e2] at hs
            simp only [Option.map_some, Option.some.injEq] at hs
            obtain ⟨c₁', hc'', hev⟩ := ih c₁.q c₁.tapes hs.symm
            refine ⟨c₁', hc'', ?_⟩
            obtain ⟨hr₁, hf₁⟩ := StateTransition.mem_eval.mp hev
            exact StateTransition.mem_eval.mpr
              ⟨Relation.ReflTransGen.head (Option.mem_def.mpr e2) hr₁, hf₁⟩
    obtain ⟨c₁, rfl, hev⟩ := aux hr q₀ (fun i => T' (e i))
      (by simp only [Equiv.apply_symm_apply])
    exact (Part.mem_map_iff _).mpr
      ⟨c₁.tapes, (Part.mem_map_iff _).mpr ⟨c₁, hev, rfl⟩, rfl⟩
  · intro hU''
    obtain ⟨T₁, hT₁, rfl⟩ := (Part.mem_map_iff _).mp hU''
    obtain ⟨c₁, hev₁, rfl⟩ := (Part.mem_map_iff _).mp hT₁
    obtain ⟨hr₁, hf₁⟩ := StateTransition.mem_eval.mp hev₁
    refine (Part.mem_map_iff _).mpr
      ⟨⟨c₁.q, fun i' => c₁.tapes (e.symm i')⟩, StateTransition.mem_eval.mpr ⟨?_, ?_⟩, rfl⟩
    · simpa only [Equiv.apply_symm_apply] using reaches_renameBank e hr₁
    · rw [kstep_renameBank]
      rw [show (fun i => (fun i' => c₁.tapes (e.symm i')) (e i)) = c₁.tapes from
        funext fun i => by simp only [Equiv.symm_apply_apply]]
      rw [(show kstep M (⟨c₁.q, c₁.tapes⟩ : KCfg Γ Λ ι) = none from hf₁)]
      rfl

variable {ΛR ΛR' : Type*}

/-- **`SemInverse` is preserved by `renameBank`.**  Renaming both legs' banks by
`e` keeps the semantic-inverse relation; the domains precompose with `e`. -/
theorem SemInverse.renameBank (e : ι ≃ ι')
    {R : KMachine Γ ΛR ι} {R' : KMachine Γ ΛR' ι}
    {q0 : ΛR} {q0' : ΛR'} {DomIn DomOut : (ι → Tape Γ) → Prop}
    (h : SemInverse R R' q0 q0' DomIn DomOut) :
    SemInverse (renameBank e R) (renameBank e R') q0 q0'
      (fun T' => DomIn (fun i => T' (e i))) (fun T' => DomOut (fun i => T' (e i))) where
  fwd := by
    intro X Y hX hY
    rw [ktapeSem_renameBank, Part.mem_map_iff] at hY
    obtain ⟨YL, hYL, rfl⟩ := hY
    rw [ktapeSem_renameBank, Part.mem_map_iff]
    refine ⟨fun i => X (e i), h.fwd _ _ hX ?_, ?_⟩
    · simpa only [Equiv.symm_apply_apply] using hYL
    · funext i'; simp [Equiv.apply_symm_apply]
  bwd := by
    intro X Y hY hX
    rw [ktapeSem_renameBank, Part.mem_map_iff] at hX
    obtain ⟨XL, hXL, rfl⟩ := hX
    rw [ktapeSem_renameBank, Part.mem_map_iff]
    refine ⟨fun i => Y (e i), h.bwd _ _ hY ?_, ?_⟩
    · simpa only [Equiv.symm_apply_apply] using hXL
    · funext i'; simp [Equiv.apply_symm_apply]

end PeriodicTM
