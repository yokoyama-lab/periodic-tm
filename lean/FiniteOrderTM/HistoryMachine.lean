/-
FiniteOrderTM/HistoryMachine.lean

Roadmap step 4, first ingredient: **the history-logging simulator** for an
arbitrary (deterministic, possibly non-reversible) k-tape machine `F`.

`histM F` is a machine on the doubled bank index `ι ⊕ Unit` (left = work,
right = history) over the enlarged alphabet `HSym Γ Λ ι = Γ ⊕ (Λ × (ι → Γ))`:
work cells carry `Γ`-letters (embedded via `Sum.inl`), history cells carry
either blank (`Sum.inl default`) or a *logged rule identity* `Sum.inr (q, a)`
— the state and full head vector at which an `F`-rule fired.  Each `F`-step
is simulated by a four-step gadget

    run q  --write (heads back, log (q,a))-->  act q a
    act q a  --F's statement on the work bank-->  post q a
    post q a  --guarded write-back (reads the log)-->  pre q'
    pre q'  --move history head right-->  run q'

The intermediate states carry the fired rule identity `(q, a)`, and every
write rule is *guarded* to fire only at the head vector it actually meets
along a simulation (blank history cell at `run`, the freshly written log at
`act`/`post`).  These guards are exactly what makes the machine backward
deterministic: the log cell under the history head identifies the unique
preimage rule at every convergence point.

Main results (all fully proved, no admitted proofs):

* `histM_reversible : KReversible (histM F)` — **unconditionally**, for
  every machine `F`.  No reversibility, halting or entry hypothesis on `F`
  whatsoever: forward determinism of `F` (it is a function) plus the logged
  rule identities are enough for backward determinism.
* `histM_respects` — the four-step gadget is a simulation in the sense of
  mathlib's `StateTransition.Respects`, so both simulation directions come
  for free (`tr_eval` / `tr_eval_rev` / `tr_eval_dom`).
* `histM_ktapeSem_proj` — **work-bank projection semantics**, as an equality
  of partial functions: projecting `⟦histM F⟧` to the work bank *is*
  `⟦F⟧` (post-composed with the alphabet embedding).
* `histM_mem_of` / `histM_mem_inv` — membership forms in both directions,
  exhibiting/recovering the history tape.
* `histM_dom_iff` — the simulator halts exactly where `F` halts.

See the roadmap-delta comment at the bottom for the honest accounting of
what is still missing towards `ReversibilisationGoal`
(InvolutoryBennett.lean).
-/
import FiniteOrderTM.Flip

namespace PeriodicTM

open Turing

variable {Γ : Type*} [Inhabited Γ]
variable {Λ : Type*}
variable {ι : Type*}

/-! ### The history alphabet and state space -/

/-- History-simulation alphabet: a work letter (`Sum.inl`), or a logged rule
identity — the machine state and full work head vector at which a rule of
the simulated machine fired (`Sum.inr`).  Blank is `Sum.inl default`. -/
abbrev HSym (Γ : Type*) (Λ : Type*) (ι : Type*) := Γ ⊕ (Λ × (ι → Γ))

instance : Inhabited (HSym Γ Λ ι) := ⟨Sum.inl default⟩

/-- States of the history simulator.  `run q` mirrors state `q` of the
simulated machine; `act`/`post` carry the identity `(q, a)` of the rule
being executed; `pre q'` is about to advance the history head. -/
inductive HState (Λ : Type*) (Γ : Type*) (ι : Type*)
  | pre (q : Λ)
  | run (q : Λ)
  | act (q : Λ) (a : ι → Γ)
  | post (q : Λ) (a : ι → Γ)

instance [Inhabited Λ] : Inhabited (HState Λ Γ ι) := ⟨.run default⟩

/-- Head vector with embedded work heads `b` and history head `s`. -/
def encH (b : ι → Γ) (s : HSym Γ Λ ι) : ι ⊕ Unit → HSym Γ Λ ι :=
  Sum.elim (fun i => Sum.inl (b i)) fun _ => s

/-- Decode the work-bank heads (junk decodes to `default`; the machine's
guards ensure junk never fires a rule). -/
def decodeW (v : ι ⊕ Unit → HSym Γ Λ ι) : ι → Γ := fun i =>
  match v (Sum.inl i) with
  | Sum.inl g => g
  | Sum.inr _ => default

@[simp] theorem decodeW_encH (b : ι → Γ) (s : HSym Γ Λ ι) :
    decodeW (encH b s) = b := rfl

omit [Inhabited Γ] in
@[simp] theorem encH_inl (b : ι → Γ) (s : HSym Γ Λ ι) (i : ι) :
    encH b s (Sum.inl i) = Sum.inl (b i) := rfl

omit [Inhabited Γ] in
@[simp] theorem encH_inr (b : ι → Γ) (s : HSym Γ Λ ι) (u : Unit) :
    encH b s (Sum.inr u) = s := rfl

/-- Move only the history bank, rightward. -/
def histRight : ι ⊕ Unit → Option Dir :=
  Sum.elim (fun _ => none) fun _ => some Dir.right

/-! ### The history-logging simulator -/

open Classical in
/-- **The history-logging simulator.**  Simulates `F` on the work banks while
logging, per simulated step, the fired rule identity `(q, a)` on the history
bank.  Noncomputable only because the write guards are classical
propositions (the bank index `ι` and alphabet are arbitrary types). -/
noncomputable def histM (F : KMachine Γ Λ ι) :
    KMachine (HSym Γ Λ ι) (HState Λ Γ ι) (ι ⊕ Unit) := fun s v =>
  match s with
  | .pre q => some (.run q, .move histRight)
  | .run q =>
      if _ : v = encH (decodeW v) default then
        match F q (decodeW v) with
        | none => none
        | some _ =>
            some (.act q (decodeW v),
              .write (encH (decodeW v) (Sum.inr (q, decodeW v))))
      else none
  | .act q a =>
      match F q a with
      | none => none
      | some (_, .write b) =>
          if _ : v = encH a (Sum.inr (q, a)) then
            some (.post q a, .write (encH b (Sum.inr (q, a))))
          else none
      | some (_, .move d) =>
          some (.post q a, .move (Sum.elim d fun _ => none))
      | some (_, .perm π) =>
          some (.post q a, .perm (Equiv.sumCongr π (Equiv.refl Unit)))
  | .post q a =>
      match F q a with
      | none => none
      | some (q', _) =>
          if _ : v (Sum.inr ()) = Sum.inr (q, a) then
            some (.pre q', .write v)
          else none

section RuleLemmas

variable {F : KMachine Γ Λ ι}

/-- The `pre` rule: advance the history head. -/
theorem histM_pre_eq (q : Λ) (v : ι ⊕ Unit → HSym Γ Λ ι) :
    histM F (.pre q) v = some (.run q, .move histRight) := rfl

theorem histM_run_enc {q : Λ} {a : ι → Γ} {r} (hF : F q a = some r) :
    histM F (.run q) (encH a default)
      = some (.act q a, .write (encH a (Sum.inr (q, a)))) := by
  simp only [histM, decodeW_encH, hF]
  exact dif_pos trivial

theorem histM_run_halt {q : Λ} {a : ι → Γ} (hF : F q a = none) :
    histM F (.run q) (encH a default) = none := by
  simp only [histM, decodeW_encH, hF]
  exact dif_pos trivial

theorem histM_act_write {q q' : Λ} {a b : ι → Γ}
    (hF : F q a = some (q', .write b)) :
    histM F (.act q a) (encH a (Sum.inr (q, a)))
      = some (.post q a, .write (encH b (Sum.inr (q, a)))) := by
  simp only [histM, hF]
  exact dif_pos trivial

theorem histM_act_move {q q' : Λ} {a : ι → Γ} {d : ι → Option Dir}
    (hF : F q a = some (q', .move d)) (v : ι ⊕ Unit → HSym Γ Λ ι) :
    histM F (.act q a) v
      = some (.post q a, .move (Sum.elim d fun _ => none)) := by
  simp only [histM, hF]

theorem histM_act_perm {q q' : Λ} {a : ι → Γ} {π : Equiv.Perm ι}
    (hF : F q a = some (q', .perm π)) (v : ι ⊕ Unit → HSym Γ Λ ι) :
    histM F (.act q a) v
      = some (.post q a, .perm (Equiv.sumCongr π (Equiv.refl Unit))) := by
  simp only [histM, hF]

theorem histM_post_fire {q q' : Λ} {a : ι → Γ} {s0 : KStmt Γ ι}
    (hF : F q a = some (q', s0)) {v : ι ⊕ Unit → HSym Γ Λ ι}
    (hv : v (Sum.inr ()) = Sum.inr (q, a)) :
    histM F (.post q a) v = some (.pre q', .write v) := by
  simp only [histM, hF, dif_pos hv]

/-! #### Rule inversion -/

theorem histM_run_some {q : Λ} {v : ι ⊕ Unit → HSym Γ Λ ι}
    {r : HState Λ Γ ι × KStmt (HSym Γ Λ ι) (ι ⊕ Unit)}
    (h : histM F (.run q) v = some r) :
    v = encH (decodeW v) default ∧
      (∃ w, F q (decodeW v) = some w) ∧
      r = (.act q (decodeW v),
        .write (encH (decodeW v) (Sum.inr (q, decodeW v)))) := by
  by_cases hv : v = encH (decodeW v) default
  · rcases hF : F q (decodeW v) with - | w
    · simp only [histM, dif_pos hv, hF] at h
      simp at h
    · simp only [histM, dif_pos hv, hF, Option.some.injEq] at h
      exact ⟨hv, ⟨w, rfl⟩, h.symm⟩
  · simp only [histM, dif_neg hv] at h
    simp at h

theorem histM_act_some {q : Λ} {a : ι → Γ} {v : ι ⊕ Unit → HSym Γ Λ ι}
    {r : HState Λ Γ ι × KStmt (HSym Γ Λ ι) (ι ⊕ Unit)}
    (h : histM F (.act q a) v = some r) :
    ∃ q' s0, F q a = some (q', s0) ∧
      ((∃ b, s0 = .write b ∧ v = encH a (Sum.inr (q, a)) ∧
          r = (.post q a, .write (encH b (Sum.inr (q, a))))) ∨
       (∃ d, s0 = .move d ∧
          r = (.post q a, .move (Sum.elim d fun _ => none))) ∨
       (∃ π, s0 = .perm π ∧
          r = (.post q a, .perm (Equiv.sumCongr π (Equiv.refl Unit))))) := by
  rcases hF : F q a with - | ⟨q', s0⟩
  · simp only [histM, hF] at h
    simp at h
  · refine ⟨q', s0, rfl, ?_⟩
    rcases s0 with b | d | π
    · by_cases hv : v = encH a (Sum.inr (q, a))
      · simp only [histM, hF, dif_pos hv, Option.some.injEq] at h
        exact Or.inl ⟨b, rfl, hv, h.symm⟩
      · simp only [histM, hF, dif_neg hv] at h
        simp at h
    · simp only [histM, hF, Option.some.injEq] at h
      exact Or.inr (Or.inl ⟨d, rfl, h.symm⟩)
    · simp only [histM, hF, Option.some.injEq] at h
      exact Or.inr (Or.inr ⟨π, rfl, h.symm⟩)

theorem histM_post_some {q : Λ} {a : ι → Γ} {v : ι ⊕ Unit → HSym Γ Λ ι}
    {r : HState Λ Γ ι × KStmt (HSym Γ Λ ι) (ι ⊕ Unit)}
    (h : histM F (.post q a) v = some r) :
    ∃ q' s0, F q a = some (q', s0) ∧ v (Sum.inr ()) = Sum.inr (q, a) ∧
      r = (.pre q', .write v) := by
  rcases hF : F q a with - | ⟨q', s0⟩
  · simp only [histM, hF] at h
    simp at h
  · by_cases hv : v (Sum.inr ()) = Sum.inr (q, a)
    · simp only [histM, hF, dif_pos hv, Option.some.injEq] at h
      exact ⟨q', s0, rfl, hv, h.symm⟩
    · simp only [histM, hF, dif_neg hv] at h
      simp at h

end RuleLemmas

/-! ### Backward determinism -/

section Reversible

variable {F : KMachine Γ Λ ι}

/-- Demands at a `run` state come only from the unique `pre` rule. -/
theorem demand_run_inv {q : Λ} {w : ι ⊕ Unit → HSym Γ Λ ι}
    {val} (h : Demand (histM F) (.run q) w val) :
    val = (.pre q, .move (revMap histRight)) := by
  cases h with
  | @write p u _ _ hr =>
      cases p with
      | pre q0 => simp [histM_pre_eq] at hr
      | run q0 =>
          obtain ⟨-, -, hr'⟩ := histM_run_some hr
          simp at hr'
      | act q0 a0 =>
          obtain ⟨q', s0, -, hbr⟩ := histM_act_some hr
          rcases hbr with ⟨b, -, -, hr'⟩ | ⟨d, -, hr'⟩ | ⟨π, -, hr'⟩ <;>
            simp at hr'
      | post q0 a0 =>
          obtain ⟨q', s0, -, -, hr'⟩ := histM_post_some hr
          simp at hr'
  | @move p u _ _ b hr =>
      cases p with
      | pre q0 =>
          rw [histM_pre_eq] at hr
          obtain ⟨h1, h2⟩ := Prod.mk.injEq .. ▸ Option.some.inj hr
          obtain rfl : q0 = q := by injection h1
          rw [KStmt.move.inj h2]
      | run q0 =>
          obtain ⟨-, -, hr'⟩ := histM_run_some hr
          simp at hr'
      | act q0 a0 =>
          obtain ⟨q', s0, -, hbr⟩ := histM_act_some hr
          rcases hbr with ⟨b', -, -, hr'⟩ | ⟨d', -, hr'⟩ | ⟨π, -, hr'⟩ <;>
            simp at hr'
      | post q0 a0 =>
          obtain ⟨q', s0, -, -, hr'⟩ := histM_post_some hr
          simp at hr'
  | @perm p u _ _ b hr =>
      cases p with
      | pre q0 => simp [histM_pre_eq] at hr
      | run q0 =>
          obtain ⟨-, -, hr'⟩ := histM_run_some hr
          simp at hr'
      | act q0 a0 =>
          obtain ⟨q', s0, -, hbr⟩ := histM_act_some hr
          rcases hbr with ⟨b', -, -, hr'⟩ | ⟨d', -, hr'⟩ | ⟨π', -, hr'⟩ <;>
            simp at hr'
      | post q0 a0 =>
          obtain ⟨q', s0, -, -, hr'⟩ := histM_post_some hr
          simp at hr'

/-- Demands at an `act` state come only from the log-write of `run`. -/
theorem demand_act_inv {q : Λ} {a : ι → Γ} {w : ι ⊕ Unit → HSym Γ Λ ι}
    {val} (h : Demand (histM F) (.act q a) w val) :
    val = (.run q, .write (encH a default)) := by
  cases h with
  | @write p u _ _ hr =>
      cases p with
      | pre q0 => simp [histM_pre_eq] at hr
      | run q0 =>
          obtain ⟨hu, -, hr'⟩ := histM_run_some hr
          obtain ⟨h1, -⟩ := Prod.mk.injEq .. ▸ hr'
          obtain ⟨e1, e2⟩ : q = q0 ∧ a = decodeW u := by
            injection h1 with e1 e2; exact ⟨e1, e2⟩
          subst e1
          rw [e2, ← hu]
      | act q0 a0 =>
          obtain ⟨q', s0, -, hbr⟩ := histM_act_some hr
          rcases hbr with ⟨b, -, -, hr'⟩ | ⟨d, -, hr'⟩ | ⟨π, -, hr'⟩ <;>
            simp at hr'
      | post q0 a0 =>
          obtain ⟨q', s0, -, -, hr'⟩ := histM_post_some hr
          simp at hr'
  | @move p u _ _ b hr =>
      cases p with
      | pre q0 => simp [histM_pre_eq] at hr
      | run q0 =>
          obtain ⟨-, -, hr'⟩ := histM_run_some hr
          simp at hr'
      | act q0 a0 =>
          obtain ⟨q', s0, -, hbr⟩ := histM_act_some hr
          rcases hbr with ⟨b', -, -, hr'⟩ | ⟨d', -, hr'⟩ | ⟨π, -, hr'⟩ <;>
            simp at hr'
      | post q0 a0 =>
          obtain ⟨q', s0, -, -, hr'⟩ := histM_post_some hr
          simp at hr'
  | @perm p u _ _ b hr =>
      cases p with
      | pre q0 => simp [histM_pre_eq] at hr
      | run q0 =>
          obtain ⟨-, -, hr'⟩ := histM_run_some hr
          simp at hr'
      | act q0 a0 =>
          obtain ⟨q', s0, -, hbr⟩ := histM_act_some hr
          rcases hbr with ⟨b', -, -, hr'⟩ | ⟨d', -, hr'⟩ | ⟨π', -, hr'⟩ <;>
            simp at hr'
      | post q0 a0 =>
          obtain ⟨q', s0, -, -, hr'⟩ := histM_post_some hr
          simp at hr'

/-- The reversed statement demanded at a `post` state, per fired rule. -/
def hinv (q : Λ) (a : ι → Γ) :
    KStmt Γ ι → KStmt (HSym Γ Λ ι) (ι ⊕ Unit)
  | .write _ => .write (encH a (Sum.inr (q, a)))
  | .move d => .move (revMap (Sum.elim d fun _ => none))
  | .perm π => .perm (Equiv.sumCongr π (Equiv.refl Unit))⁻¹

/-- Demands at a `post` state come only from the `act` rule of the same
fired rule identity; the demanded value is a function of `F q a`. -/
theorem demand_post_inv {q : Λ} {a : ι → Γ} {w : ι ⊕ Unit → HSym Γ Λ ι}
    {val} (h : Demand (histM F) (.post q a) w val) :
    ∃ q' s0, F q a = some (q', s0) ∧ val = (.act q a, hinv q a s0) := by
  cases h with
  | @write p u _ _ hr =>
      cases p with
      | pre q0 => simp [histM_pre_eq] at hr
      | run q0 =>
          obtain ⟨-, -, hr'⟩ := histM_run_some hr
          simp at hr'
      | act q0 a0 =>
          obtain ⟨q', s0, hF, hbr⟩ := histM_act_some hr
          rcases hbr with ⟨b, hs0, hu, hr'⟩ | ⟨d, -, hr'⟩ | ⟨π, -, hr'⟩
          · obtain ⟨h1, -⟩ := Prod.mk.injEq .. ▸ hr'
            obtain ⟨e1, e2⟩ : q = q0 ∧ a = a0 := by
              injection h1 with e1 e2; exact ⟨e1, e2⟩
            subst e1; subst e2
            exact ⟨q', s0, hF, by rw [hs0]; simp only [hinv]; rw [hu]⟩
          · simp at hr'
          · simp at hr'
      | post q0 a0 =>
          obtain ⟨q', s0, -, -, hr'⟩ := histM_post_some hr
          simp at hr'
  | @move p u _ _ b hr =>
      cases p with
      | pre q0 => simp [histM_pre_eq] at hr
      | run q0 =>
          obtain ⟨-, -, hr'⟩ := histM_run_some hr
          simp at hr'
      | act q0 a0 =>
          obtain ⟨q', s0, hF, hbr⟩ := histM_act_some hr
          rcases hbr with ⟨b', -, -, hr'⟩ | ⟨d, hs0, hr'⟩ | ⟨π, -, hr'⟩
          · simp at hr'
          · obtain ⟨h1, h2⟩ := Prod.mk.injEq .. ▸ hr'
            obtain ⟨e1, e2⟩ : q = q0 ∧ a = a0 := by
              injection h1 with e1 e2; exact ⟨e1, e2⟩
            subst e1; subst e2
            exact ⟨q', s0, hF,
              by rw [hs0]; simp only [hinv]; rw [KStmt.move.inj h2]⟩
          · simp at hr'
      | post q0 a0 =>
          obtain ⟨q', s0, -, -, hr'⟩ := histM_post_some hr
          simp at hr'
  | @perm p u _ _ b hr =>
      cases p with
      | pre q0 => simp [histM_pre_eq] at hr
      | run q0 =>
          obtain ⟨-, -, hr'⟩ := histM_run_some hr
          simp at hr'
      | act q0 a0 =>
          obtain ⟨q', s0, hF, hbr⟩ := histM_act_some hr
          rcases hbr with ⟨b', -, -, hr'⟩ | ⟨d, -, hr'⟩ | ⟨π, hs0, hr'⟩
          · simp at hr'
          · simp at hr'
          · obtain ⟨h1, h2⟩ := Prod.mk.injEq .. ▸ hr'
            obtain ⟨e1, e2⟩ : q = q0 ∧ a = a0 := by
              injection h1 with e1 e2; exact ⟨e1, e2⟩
            subst e1; subst e2
            exact ⟨q', s0, hF,
              by rw [hs0]; simp only [hinv]; rw [KStmt.perm.inj h2]⟩
      | post q0 a0 =>
          obtain ⟨q', s0, -, -, hr'⟩ := histM_post_some hr
          simp at hr'

/-- Demands at a `pre` state come only from guarded write-backs, whose
reading of the log cell pins the fired rule identity to the slot heads. -/
theorem demand_pre_inv {p : Λ} {w : ι ⊕ Unit → HSym Γ Λ ι}
    {val} (h : Demand (histM F) (.pre p) w val) :
    ∃ q a, w (Sum.inr ()) = Sum.inr (q, a) ∧
      val = (.post q a, .write w) := by
  cases h with
  | @write p' u _ _ hr =>
      cases p' with
      | pre q0 => simp [histM_pre_eq] at hr
      | run q0 =>
          obtain ⟨-, -, hr'⟩ := histM_run_some hr
          simp at hr'
      | act q0 a0 =>
          obtain ⟨q', s0, -, hbr⟩ := histM_act_some hr
          rcases hbr with ⟨b, -, -, hr'⟩ | ⟨d, -, hr'⟩ | ⟨π, -, hr'⟩ <;>
            simp at hr'
      | post q0 a0 =>
          obtain ⟨q', s0, -, hu, hr'⟩ := histM_post_some hr
          obtain ⟨-, h2⟩ := Prod.mk.injEq .. ▸ hr'
          obtain rfl : w = u := KStmt.write.inj h2
          exact ⟨q0, a0, hu, rfl⟩
  | @move p' u _ _ b hr =>
      cases p' with
      | pre q0 =>
          rw [histM_pre_eq] at hr
          obtain ⟨h1, -⟩ := Prod.mk.injEq .. ▸ Option.some.inj hr
          simp at h1
      | run q0 =>
          obtain ⟨-, -, hr'⟩ := histM_run_some hr
          simp at hr'
      | act q0 a0 =>
          obtain ⟨q', s0, -, hbr⟩ := histM_act_some hr
          rcases hbr with ⟨b', -, -, hr'⟩ | ⟨d', -, hr'⟩ | ⟨π, -, hr'⟩ <;>
            simp at hr'
      | post q0 a0 =>
          obtain ⟨q', s0, -, -, hr'⟩ := histM_post_some hr
          simp at hr'
  | @perm p' u _ _ b hr =>
      cases p' with
      | pre q0 => simp [histM_pre_eq] at hr
      | run q0 =>
          obtain ⟨-, -, hr'⟩ := histM_run_some hr
          simp at hr'
      | act q0 a0 =>
          obtain ⟨q', s0, -, hbr⟩ := histM_act_some hr
          rcases hbr with ⟨b', -, -, hr'⟩ | ⟨d', -, hr'⟩ | ⟨π', -, hr'⟩ <;>
            simp at hr'
      | post q0 a0 =>
          obtain ⟨q', s0, -, -, hr'⟩ := histM_post_some hr
          simp at hr'

/-- **The history simulator is syntactically reversible — unconditionally.**
No hypothesis on `F` at all: forward determinism of `F` (it is a function)
plus the per-step rule-identity log make the demands single-valued, and all
move/perm rules of the gadget are head-independent by construction. -/
theorem histM_reversible (F : KMachine Γ Λ ι) : KReversible (histM F) where
  backdet := by
    intro t w v₁ v₂ h₁ h₂
    cases t with
    | pre p =>
        obtain ⟨q₁, a₁, hw₁, rfl⟩ := demand_pre_inv h₁
        obtain ⟨q₂, a₂, hw₂, rfl⟩ := demand_pre_inv h₂
        obtain ⟨rfl, rfl⟩ : q₁ = q₂ ∧ a₁ = a₂ := by
          have := (hw₁.symm.trans hw₂)
          injection this with e
          exact ⟨congrArg Prod.fst e, congrArg Prod.snd e⟩
        rfl
    | run q => rw [demand_run_inv h₁, demand_run_inv h₂]
    | act q a => rw [demand_act_inv h₁, demand_act_inv h₂]
    | post q a =>
        obtain ⟨q₁, s₁, hF₁, rfl⟩ := demand_post_inv h₁
        obtain ⟨q₂, s₂, hF₂, rfl⟩ := demand_post_inv h₂
        obtain ⟨-, rfl⟩ : q₁ = q₂ ∧ s₁ = s₂ := by
          have := Option.some.inj (hF₁.symm.trans hF₂)
          exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
        rfl
  move_uniform := by
    intro p v t d hr v'
    cases p with
    | pre q =>
        rw [histM_pre_eq] at hr
        obtain ⟨h1, h2⟩ := Prod.mk.injEq .. ▸ Option.some.inj hr
        rw [histM_pre_eq, h1, h2]
    | run q =>
        obtain ⟨-, -, hr'⟩ := histM_run_some hr
        simp at hr'
    | act q a =>
        obtain ⟨q', s0, hF, hbr⟩ := histM_act_some hr
        rcases hbr with ⟨b, -, -, hr'⟩ | ⟨d', hs0, hr'⟩ | ⟨π, -, hr'⟩
        · simp at hr'
        · obtain ⟨h1, h2⟩ := Prod.mk.injEq .. ▸ hr'
          rw [hs0] at hF
          rw [histM_act_move hF v', h1, h2]
        · simp at hr'
    | post q a =>
        obtain ⟨q', s0, -, -, hr'⟩ := histM_post_some hr
        simp at hr'
  perm_uniform := by
    intro p v t π hr v'
    cases p with
    | pre q => simp [histM_pre_eq] at hr
    | run q =>
        obtain ⟨-, -, hr'⟩ := histM_run_some hr
        simp at hr'
    | act q a =>
        obtain ⟨q', s0, hF, hbr⟩ := histM_act_some hr
        rcases hbr with ⟨b, -, -, hr'⟩ | ⟨d, -, hr'⟩ | ⟨π', hs0, hr'⟩
        · simp at hr'
        · simp at hr'
        · obtain ⟨h1, h2⟩ := Prod.mk.injEq .. ▸ hr'
          rw [hs0] at hF
          rw [histM_act_perm hF v', h1, h2]
    | post q a =>
        obtain ⟨q', s0, -, -, hr'⟩ := histM_post_some hr
        simp at hr'

end Reversible

/-! ### Simulation: the four-step gadget -/

/-- The alphabet embedding `Γ ↪ HSym Γ Λ ι` as a pointed map. -/
def hsymEmb : PointedMap Γ (HSym Γ Λ ι) :=
  ⟨(Sum.inl : Γ → HSym Γ Λ ι), rfl⟩

/-- Embed a work-bank of `F` and adjoin a history tape. -/
def embedT (X : ι → Tape Γ) (h : Tape (HSym Γ Λ ι)) :
    ι ⊕ Unit → Tape (HSym Γ Λ ι) :=
  Sum.elim (fun i => (X i).map hsymEmb) fun _ => h

@[simp] theorem embedT_inl (X : ι → Tape Γ) (h : Tape (HSym Γ Λ ι)) (i : ι) :
    embedT X h (Sum.inl i) = (X i).map hsymEmb := rfl

@[simp] theorem embedT_inr (X : ι → Tape Γ) (h : Tape (HSym Γ Λ ι)) (u : Unit) :
    embedT X h (Sum.inr u) = h := rfl

theorem headsV_embedT (X : ι → Tape Γ) (h : Tape (HSym Γ Λ ι)) :
    headsV (embedT X h) = encH (headsV X) h.1 := by
  funext j
  rcases j with i | u
  · exact Tape.map_fst hsymEmb (X i)
  · rfl

section Fresh

variable {Γ' : Type*} [Inhabited Γ']

/-- A *fresh* history tape: blank under the head and blank to the right.
Both properties are preserved by one write-then-move-right gadget round. -/
def Fresh (h : Tape Γ') : Prop := h.1 = default ∧ h.right = default

theorem fresh_write_move {h : Tape Γ'} (hf : Fresh h) (s : Γ') :
    Fresh ((h.write s).move Dir.right) := by
  obtain ⟨hd, L, R⟩ := h
  obtain ⟨-, h2⟩ := hf
  have hR : R = default := h2
  subst hR
  constructor
  · show (default : ListBlank Γ').head = default
    rfl
  · show (default : ListBlank Γ').tail = default
    rfl

end Fresh

section Gadget

variable {F : KMachine Γ Λ ι}

/-- Work tapes are untouched by writing back their own (embedded) heads. -/
theorem embed_write_self (X : ι → Tape Γ) (i : ι) :
    ((X i).map (hsymEmb (Λ := Λ) (ι := ι))).write (Sum.inl (headsV X i))
      = (X i).map (hsymEmb (Λ := Λ) (ι := ι)) := by
  have : (Sum.inl (headsV X i) : HSym Γ Λ ι) = ((X i).map hsymEmb).1 :=
    (Tape.map_fst hsymEmb (X i)).symm
  rw [this, Tape.write_self]

/-- Applying the log-write to an embedded bank: work banks untouched,
history head overwritten with the log symbol. -/
theorem apply_logwrite (X : ι → Tape Γ) (h : Tape (HSym Γ Λ ι)) (s : HSym Γ Λ ι) :
    (KStmt.write (encH (headsV X) s)).apply (embedT X h)
      = embedT X (h.write s) := by
  funext j
  rcases j with i | u
  · exact embed_write_self X i
  · rfl

/-- Applying (the inflation of) an `F`-statement to an embedded bank
commutes with the embedding. -/
theorem apply_embed_stmt (s0 : KStmt Γ ι) (X : ι → Tape Γ)
    (h : Tape (HSym Γ Λ ι)) :
    (match s0 with
      | .write b =>
          (KStmt.write (encH b h.1)).apply (embedT X h)
      | .move d =>
          (KStmt.move (Sum.elim d fun _ => none)).apply (embedT X h)
      | .perm π =>
          (KStmt.perm (Equiv.sumCongr π (Equiv.refl Unit))).apply
            (embedT X h))
      = embedT (s0.apply X) h := by
  rcases s0 with b | d | π
  · funext j
    rcases j with i | u
    · show ((X i).map hsymEmb).write (Sum.inl (b i)) = ((X i).write (b i)).map hsymEmb
      rw [Tape.map_write]
      rfl
    · exact Tape.write_self h
  · funext j
    rcases j with i | u
    · show (KStmt.move _).apply (embedT X h) (Sum.inl i)
        = ((KStmt.move d).apply X i).map hsymEmb
      rcases hd : d i with - | dir <;>
        simp [KStmt.apply, hd, Tape.map_move]
    · rfl
  · funext j
    rcases j with i | u
    · show embedT X h ((Equiv.sumCongr π (Equiv.refl Unit))⁻¹ (Sum.inl i))
        = (X (π⁻¹ i)).map hsymEmb
      simp
    · show embedT X h ((Equiv.sumCongr π (Equiv.refl Unit))⁻¹ (Sum.inr u))
        = h
      simp

/-- **The four-step gadget**: one `F`-step is simulated by exactly the
run–act–post–pre round, logging the fired rule identity and advancing the
history head one cell to the right. -/
theorem histM_gadget {q q' : Λ} {s0 : KStmt Γ ι} {X : ι → Tape Γ}
    (hF : F q (headsV X) = some (q', s0)) {h : Tape (HSym Γ Λ ι)}
    (hf : Fresh h) :
    StateTransition.Reaches₁ (kstep (histM F))
      ⟨.run q, embedT X h⟩
      ⟨.run q', embedT (s0.apply X)
        ((h.write (Sum.inr (q, headsV X))).move Dir.right)⟩ := by
  set a := headsV X with ha
  set hL : Tape (HSym Γ Λ ι) := h.write (Sum.inr (q, a)) with hhL
  -- step 1: log-write
  have hheads0 : headsV (embedT X h) = encH a default := by
    rw [headsV_embedT, hf.1]
  have step1 : kstep (histM F) ⟨.run q, embedT X h⟩
      = some ⟨.act q a, embedT X hL⟩ := by
    rw [kstep, hheads0, histM_run_enc hF]
    exact congrArg some (congrArg _ (apply_logwrite X h _))
  -- after the log-write the history head reads the log
  have hL1 : hL.1 = Sum.inr (q, a) := rfl
  have hheads1 : headsV (embedT X hL) = encH a (Sum.inr (q, a)) := by
    rw [headsV_embedT, hL1]
  -- step 2: perform the F-statement on the work bank
  have step2 : kstep (histM F) ⟨.act q a, embedT X hL⟩
      = some ⟨.post q a, embedT (s0.apply X) hL⟩ := by
    rcases s0 with b | d | π
    · rw [kstep, hheads1, histM_act_write hF]
      refine congrArg some (congrArg _ ?_)
      have := apply_embed_stmt (.write b) X hL
      rwa [hL1] at this
    · rw [kstep, hheads1, histM_act_move hF]
      exact congrArg some (congrArg _ (apply_embed_stmt (.move d) X hL))
    · rw [kstep, hheads1, histM_act_perm hF]
      exact congrArg some (congrArg _ (apply_embed_stmt (.perm π) X hL))
  -- step 3: write-back (a no-op on the tapes), converging on the log cell
  have hheads2 : headsV (embedT (s0.apply X) hL) (Sum.inr ())
      = Sum.inr (q, a) := hL1
  have step3 : kstep (histM F) ⟨.post q a, embedT (s0.apply X) hL⟩
      = some ⟨.pre q', embedT (s0.apply X) hL⟩ := by
    rw [kstep, histM_post_fire hF hheads2]
    exact congrArg some (congrArg _ (write_heads_apply _))
  -- step 4: advance the history head
  have step4 : kstep (histM F) ⟨.pre q', embedT (s0.apply X) hL⟩
      = some ⟨.run q', embedT (s0.apply X) (hL.move Dir.right)⟩ := by
    rw [kstep, histM_pre_eq]
    refine congrArg some (congrArg _ ?_)
    funext j
    rcases j with i | u
    · rfl
    · rfl
  exact Relation.TransGen.head (Option.mem_def.mpr step1)
    (Relation.TransGen.head' (Option.mem_def.mpr step2)
      (Relation.ReflTransGen.head (Option.mem_def.mpr step3)
        (Relation.ReflTransGen.single (Option.mem_def.mpr step4))))

/-- The simulation relation: an `F`-configuration corresponds to the
`run`-state configuration with embedded work banks and *some* fresh history
tape. -/
def htr (_F : KMachine Γ Λ ι) :
    KCfg Γ Λ ι → KCfg (HSym Γ Λ ι) (HState Λ Γ ι) (ι ⊕ Unit) → Prop :=
  fun c d => ∃ h, Fresh h ∧ d = ⟨.run c.q, embedT c.tapes h⟩

/-- **The gadget is a `Respects`-simulation** in the sense of mathlib's
`StateTransition` theory: each `F`-step maps to one-or-more `histM F`-steps
re-establishing the relation, and `F`-halting configurations map to
`histM F`-halting configurations. -/
theorem histM_respects (F : KMachine Γ Λ ι) :
    StateTransition.Respects (kstep F) (kstep (histM F)) (htr F) := by
  rintro ⟨q, X⟩ d ⟨h, hf, rfl⟩
  rcases e : kstep F ⟨q, X⟩ with - | c'
  · -- F halts here; so does the simulator, at the same `run` state
    rw [kstep_eq_none_iff] at e
    show kstep (histM F) ⟨.run q, embedT X h⟩ = none
    rw [kstep_eq_none_iff]
    show histM F (.run q) (headsV (embedT X h)) = none
    rw [headsV_embedT, hf.1]
    exact histM_run_halt e
  · -- F steps; run the gadget
    obtain ⟨⟨q', s0⟩, hF, hc'⟩ :
        ∃ r, F q (headsV X) = some r ∧ c' = ⟨r.1, r.2.apply X⟩ := by
      rcases eF : F q (headsV X) with - | r
      · rw [kstep, eF] at e; cases e
      · rw [kstep, eF] at e
        exact ⟨r, rfl, (Option.some.inj e).symm⟩
    subst hc'
    exact ⟨⟨.run q', embedT (s0.apply X)
        ((h.write (Sum.inr (q, headsV X))).move Dir.right)⟩,
      ⟨_, fresh_write_move hf _, rfl⟩,
      histM_gadget hF hf⟩

end Gadget

/-! ### Projection semantics -/

section Semantics

variable {F : KMachine Γ Λ ι}

/-- Forward simulation, membership form: every halting `F`-run is realised
by the simulator, with the embedded output on the work bank and some fresh
final history tape. -/
theorem histM_mem_of {q0 : Λ} {X Y : ι → Tape Γ}
    (hY : Y ∈ ktapeSem F q0 X) {h : Tape (HSym Γ Λ ι)} (hf : Fresh h) :
    ∃ h', Fresh h' ∧
      embedT Y h' ∈ ktapeSem (histM F) (.run q0) (embedT X h) := by
  obtain ⟨c, hc, rfl⟩ := (Part.mem_map_iff _).mp hY
  obtain ⟨d, hd, hde⟩ := StateTransition.tr_eval (histM_respects F)
    (⟨h, hf, rfl⟩ : htr F ⟨q0, X⟩ ⟨.run q0, embedT X h⟩) hc
  obtain ⟨h', hf', rfl⟩ := hd
  exact ⟨h', hf', (Part.mem_map_iff _).mpr ⟨_, hde, rfl⟩⟩

/-- Backward simulation, membership form: every halting run of the simulator
(from an embedded input with fresh history) is the image of a halting
`F`-run. -/
theorem histM_mem_inv {q0 : Λ} {X : ι → Tape Γ}
    {h : Tape (HSym Γ Λ ι)} (hf : Fresh h)
    {U : ι ⊕ Unit → Tape (HSym Γ Λ ι)}
    (hU : U ∈ ktapeSem (histM F) (.run q0) (embedT X h)) :
    ∃ Y ∈ ktapeSem F q0 X, ∃ h', Fresh h' ∧ U = embedT Y h' := by
  obtain ⟨d, hd, rfl⟩ := (Part.mem_map_iff _).mp hU
  obtain ⟨c, hc, hce⟩ := StateTransition.tr_eval_rev (histM_respects F)
    (⟨h, hf, rfl⟩ : htr F ⟨q0, X⟩ ⟨.run q0, embedT X h⟩) hd
  obtain ⟨h', hf', rfl⟩ := hc
  exact ⟨c.tapes, (Part.mem_map_iff _).mpr ⟨c, hce, rfl⟩, h', hf', rfl⟩

/-- **Work-bank projection semantics** (equality of partial functions):
projecting the simulator's semantics to the work bank *is* the semantics of
`F`, post-composed with the alphabet embedding.  No hypothesis on `F`. -/
theorem histM_ktapeSem_proj (F : KMachine Γ Λ ι) (q0 : Λ) (X : ι → Tape Γ)
    {h : Tape (HSym Γ Λ ι)} (hf : Fresh h) :
    (ktapeSem (histM F) (.run q0) (embedT X h)).map (fun U => U ∘ Sum.inl)
      = (ktapeSem F q0 X).map (fun Y i => (Y i).map hsymEmb) := by
  ext V
  constructor
  · intro hV
    obtain ⟨U, hU, rfl⟩ := (Part.mem_map_iff _).mp hV
    obtain ⟨Y, hY, h', -, rfl⟩ := histM_mem_inv hf hU
    exact (Part.mem_map_iff _).mpr ⟨Y, hY, rfl⟩
  · intro hV
    obtain ⟨Y, hY, rfl⟩ := (Part.mem_map_iff _).mp hV
    obtain ⟨h', -, hmem⟩ := histM_mem_of hY hf
    exact (Part.mem_map_iff _).mpr ⟨embedT Y h', hmem, rfl⟩

/-- The simulator halts exactly where `F` halts. -/
theorem histM_dom_iff (F : KMachine Γ Λ ι) (q0 : Λ) (X : ι → Tape Γ)
    {h : Tape (HSym Γ Λ ι)} (hf : Fresh h) :
    (ktapeSem (histM F) (.run q0) (embedT X h)).Dom
      ↔ (ktapeSem F q0 X).Dom :=
  StateTransition.tr_eval_dom (histM_respects F) ⟨h, hf, rfl⟩

end Semantics

/-!
### Roadmap delta (step 4 ingredient: the history-logging simulator)

**Done here (all fully verified, no admitted proofs):**
* The history-logging simulator `histM F` for an *arbitrary* deterministic
  `F : KMachine Γ Λ ι` — the "fresh machine construction" that the roadmap
  delta of `InvolutoryBennett.lean` names as the sole missing ingredient of
  `ReversibilisationGoal`.  Because a `KMachine` rule acts on the whole bank
  in one step but a `write` cannot be combined with a `move`, the per-step
  log is realised by a four-state gadget (`run`/`act`/`post`/`pre`) with the
  fired rule identity `(q, a)` carried in the intermediate states, written
  to the history cell, and *re-read* by the guarded write-back before the
  history head advances — this ordering is what lets distinct rules
  converging on the same `F`-state be told apart backwards.
* `histM_reversible`: `KReversible (histM F)` with **no hypotheses on `F`**.
* `histM_respects` + `histM_gadget`: the simulation, packaged as a mathlib
  `StateTransition.Respects` witness, giving both directions at once.
* `histM_ktapeSem_proj`: `⟦histM F⟧` projected to the work bank equals
  `⟦F⟧` (up to the alphabet embedding `hsymEmb`), as an equality of partial
  functions; `histM_mem_of` / `histM_mem_inv` are the membership forms and
  `histM_dom_iff` the domain equality.

**Honest accounting — what this does *not* yet give:**
1. `histM F` satisfies `KReversible` but **not** the halt/entry discipline
   consumed by `flipM_tapeSem_inverse` / `bennettWith_mem`:
   * halting is not concentrated in one state (`∀ q a, M q a = none ↔ q = qf`
     fails: the simulator also halts at guard violations, e.g. `run` states
     over non-embedded head vectors, and at every `act`/`post` state whose
     rule identity `F q a = none`);
   * the entry condition `(∃ v, Demand M q b v) ↔ q ≠ q₀` fails: `act`/`post`
     states are demanded only at their guard head vectors, and `run q` states
     are demanded at every `b` even though a simulation only ever enters them
     with a fresh history cell.
   The fix is a domain-restricted (`SemInverse`-style) statement: build
   `flipM (histM F) σ` anyway (it exists — `KReversible` is all `flipM`
   needs) and prove inverse-semantics *on the reachable configurations*
   (embedded work bank + fresh history), by reversing the gadget rounds
   directly rather than through `flipM_tapeSem_inverse`.  That reversal
   proof is the next missing lemma, and it is precisely the `SemInverse`
   witness `ReversibilisationGoal` asks for.
2. `ReversibilisationGoal` itself also needs (i) the `Unit`-bank collapse:
   `histM` lives on `ι ⊕ Unit`, while `Reversibilisation` wants a
   `Unit`-bank machine with the same `stringSem` as a `TM0` machine `R` —
   so either a 2-bank-to-1-bank encoding, or a restatement of the goal at
   bank level; and (ii) Bennett's uncompute phase to erase the history
   (using the semantic inverse `R'`), which consumes the hypothesis
   `⟦R⟧⁻¹ = ⟦R'⟧`.  Neither is attempted here.
3. The history *content* is only carried existentially (`Fresh h'`): no
   closed form of the final history tape (the list of logged rule
   identities) is proved.  Uncomputing will need at least the fact that the
   final history tape determines the run; that is future work.
-/

end PeriodicTM
