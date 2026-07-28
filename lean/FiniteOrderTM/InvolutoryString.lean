/-
FiniteOrderTM/InvolutoryString.lean

Roadmap step 1 for `CompletenessGoal` (see `Involutory.lean`): the
string/IO-encoding bridge.  Lifts the one-cell involutory result from
tape semantics (`tapeSem`) to string semantics (`stringSem`, the
Axelsen–Glück standard-configuration convention of `IOConvention.lean`).

Contents:

* `StringInvolutory M q₀` — `stringSem M q₀` is a partial involution on
  strings; the string-level notion of "computes an involution".

* `SyntacticallyInvolutory.stringInvolutory` — closure lemma (a): a
  syntactically involutory machine with standard output computes a
  partial involution *on strings* (soundness of the syntactic condition
  at the encoding level; wraps `stringSem_involutive`).

* `applyHead g` / `stringSem_writeHead` — the string function computed
  by the one-cell writer is exactly "apply `g` to the first symbol"
  (`applyHead`), *totally* and with no hypotheses on `g`.  This is the
  strongest reachable statement with the existing combinators: the
  per-symbol map on the whole string would need a right-sweep machine
  plus a return sweep (a genuinely new construction, deferred to
  roadmap steps 2–3), whereas the first-symbol involution is complete
  for the one-cell kernel already proved.

* `applyHead_involutive`, `stringInvolutory_writeHead` — if `g` is an
  involution then `applyHead g` is an involution on `List Γ`, and
  `writeHead g` is string-involutory *without* the blank-fixing
  hypothesis `g default = default` (which `StdOutput` needs; the direct
  computation `stringSem_writeHead` bypasses it).

* `completenessGoal_oneCell_string` — the string-level one-cell
  completeness instance: every involution `g` on the alphabet induces a
  string involution `applyHead g`, computed totally by a syntactically
  involutory machine.

* `StringCompletenessGoal` — the encoding-aware restatement of
  `CompletenessGoal` demanded by roadmap step 1: agreement of
  `stringSem` (not strict `tapeSem` equality).

* Conjugation closure (b): `conj_stringPartialInvolution` proves the
  *semantic* string-level closure (conjugating a partial string
  involution by an invertible partial string map yields a partial
  string involution — pure `Part` algebra, mirroring the proof shape of
  `conj_partial_involution` in `Symmetrise.lean`);
  `StringConjugationClosure` states the *machine-level* closure as a
  `Prop` (the KMachine-level witnesses `conjSem` / `conj_KInvolutory` /
  `conj_partial_involution` exist in `Symmetrise.lean`, but transporting
  them to single-tape `stringSem` needs the `Lift`/`Reindex` transport
  plus a `StdOutput` argument for the seq-machine — deferred).
-/
import FiniteOrderTM.Involutory
import FiniteOrderTM.IOConventionInstance

namespace PeriodicTM

open Turing Turing.TM0

variable {Γ : Type*} [Inhabited Γ] {Λ : Type*} [Inhabited Λ]

/-! ### String-level involutority -/

/-- **String-level involutority**: the string semantics of `M` at `q₀` is a
partial involution on `List Γ`.  This is the notion of "computes an
involution" appropriate to the I/O convention of `IOConvention.lean`. -/
def StringInvolutory (M : Machine Γ Λ) (q₀ : Λ) : Prop :=
  ∀ s s', s' ∈ stringSem M q₀ s → s ∈ stringSem M q₀ s'

/-- **Closure lemma (a)**: a syntactically involutory machine with standard
output computes a partial involution on strings.  Soundness of the syntactic
condition at the encoding level; the `σ`-witness is extracted and handed to
`stringSem_involutive`. -/
theorem SyntacticallyInvolutory.stringInvolutory {M : Machine Γ Λ}
    {q₀ qf : Λ} (h : SyntacticallyInvolutory M q₀ qf)
    (hSO : StdOutput M q₀) : StringInvolutory M q₀ := by
  obtain ⟨σ, hσ⟩ := h
  exact stringSem_involutive hσ hSO

/-! ### The string function of the one-cell writer -/

/-- Apply `g` to the first symbol of a string (identity on `[]`).  This is
the string involution induced by an alphabet involution `g` under the
standard-configuration encoding — exactly what the one-cell writer
`writeHead g` computes at string level. -/
def applyHead (g : Γ → Γ) : List Γ → List Γ
  | [] => []
  | a :: t => g a :: t

omit [Inhabited Γ] in
@[simp] theorem applyHead_nil (g : Γ → Γ) : applyHead g ([] : List Γ) = [] :=
  rfl

omit [Inhabited Γ] in
@[simp] theorem applyHead_cons (g : Γ → Γ) (a : Γ) (t : List Γ) :
    applyHead g (a :: t) = g a :: t := rfl

omit [Inhabited Γ] in
/-- If `g` is an involution on the alphabet then `applyHead g` is an
involution on strings. -/
theorem applyHead_involutive (g : Γ → Γ) (hg : ∀ a, g (g a) = a)
    (s : List Γ) : applyHead g (applyHead g s) = s := by
  cases s with
  | nil => rfl
  | cons a t => simp [hg]

/-- The head symbol of a standard tape for a nonempty string. -/
theorem mk1_head_cons (a : Γ) (t : List Γ) : (Tape.mk₁ (a :: t)).1 = a := by
  simp [Tape.mk₁, Tape.mk₂, Tape.mk']

/-- **String semantics of the one-cell writer**: `writeHead g` computes the
total string function `applyHead g` ("apply `g` to the first symbol").
No hypotheses on `g`: the `[]` case reads zero symbols, so blank-fixing is
not needed for the computation (only `StdOutput` needs it). -/
theorem stringSem_writeHead (g : Γ → Γ) (s : List Γ) :
    stringSem (writeHead g) false s = Part.some (applyHead g s) := by
  rw [stringSem, tapeSem_writeHead, Part.map_some]
  cases s with
  | nil => rfl
  | cons a t =>
    rw [mk1_head_cons, mk1_write]
    simp only [List.tail_cons, applyHead_cons]
    rw [show (a :: t).length = (g a :: t).length from rfl, readTape_mk₁]

/-- If `g` is an involution then `writeHead g` is string-involutory —
directly from the computed semantics, with no blank-fixing hypothesis
(contrast `stringSem_writeHead_involutive` in `IOConventionInstance.lean`,
which goes through `StdOutput` and needs `g default = default`). -/
theorem stringInvolutory_writeHead (g : Γ → Γ) (hg : ∀ a, g (g a) = a) :
    StringInvolutory (writeHead g) false := by
  intro s s' hs'
  rw [stringSem_writeHead, Part.mem_some_iff] at hs'
  subst hs'
  rw [stringSem_writeHead, applyHead_involutive g hg, Part.mem_some_iff]

/-- **One-cell completeness at string level**: every involution `g` on the
alphabet induces the string involution `applyHead g`, and it is computed
totally by a syntactically involutory machine — the string-level lift of
`completenessGoal_oneCell`. -/
theorem completenessGoal_oneCell_string (g : Γ → Γ)
    (hg : ∀ a, g (g a) = a) :
    ∃ (M : Machine Γ Bool) (q₀ qf : Bool),
      SyntacticallyInvolutory M q₀ qf ∧
      ∀ s : List Γ, stringSem M q₀ s = Part.some (applyHead g s) :=
  ⟨writeHead g, false, true,
    (syntacticallyInvolutory_writeHead_iff g).mpr hg, stringSem_writeHead g⟩

/-! ### The encoding-aware completeness target -/

/-- **Encoding-aware restatement of `CompletenessGoal`** (roadmap step 1):
every partial *string* involution computed by some machine (w.r.t. the
standard-configuration I/O convention) is computed, at `stringSem` level, by
a syntactically involutory machine on a possibly enlarged state space.  This
replaces the strict `tapeSem` equality of `CompletenessGoal` by agreement of
string semantics, which is the form Nakano's 2k-tape construction can
actually satisfy (the history tapes are hidden by the encoding). -/
def StringCompletenessGoal : Prop :=
  ∀ (Γ Λ : Type) [Inhabited Γ] [Inhabited Λ]
    (M : Machine Γ Λ) (q₀ qf : Λ),
    (∀ q a, M q a = none ↔ q = qf) →
    StringInvolutory M q₀ →
    ∃ (Λ' : Type) (_ : Inhabited Λ') (M' : Machine Γ Λ') (q₀' qf' : Λ'),
      SyntacticallyInvolutory M' q₀' qf' ∧
      ∀ s, stringSem M' q₀' s = stringSem M q₀ s

/-! ### Conjugation closure at string level -/

omit [Inhabited Γ] in
/-- **Closure lemma (b), semantic form**: conjugating a partial string
involution `f` by an invertible partial string map (`h` with inverse `h'`)
yields a partial string involution `h' ∘ f ∘ h`.  Pure `Part` algebra,
mirroring the proof of `conj_partial_involution` in `Symmetrise.lean`; this
is the string-level shadow of Nakano's Lemma 4.4 and applies in particular
with `h = stringSem R r₀`, `h' = stringSem R' r₀'` for mutually inverse
machines. -/
theorem conj_stringPartialInvolution
    {f h h' : List Γ → Part (List Γ)}
    (hf : ∀ s t, t ∈ f s → s ∈ f t)
    (hinv : ∀ s t, t ∈ h s ↔ s ∈ h' t) :
    ∀ s t, t ∈ (h s).bind (fun u => (f u).bind h') →
      s ∈ (h t).bind (fun u => (f u).bind h') := by
  intro s t ht
  rw [Part.mem_bind_iff] at ht
  obtain ⟨u, hu, htf⟩ := ht
  rw [Part.mem_bind_iff] at htf
  obtain ⟨v, hv, htv⟩ := htf
  -- hu : u ∈ h s ; hv : v ∈ f u ; htv : t ∈ h' v
  have hvt : v ∈ h t := (hinv t v).mpr htv
  have huv : u ∈ f v := hf u v hv
  have hsu : s ∈ h' u := (hinv s u).mp hu
  exact Part.mem_bind_iff.mpr ⟨v, hvt, Part.mem_bind_iff.mpr ⟨u, huv, hsu⟩⟩

/-- **Closure lemma (b), machine form — statement only**: if `M` is
syntactically involutory and `R`, `R'` compute mutually inverse partial
string functions, then some syntactically involutory machine computes the
string conjugation `⟦R'⟧ ∘ ⟦M⟧ ∘ ⟦R⟧`.

The KMachine-level witnesses exist in `Symmetrise.lean` (`conjSem` for the
threefold composition, `conj_KInvolutory` for syntactic involutority of
`seq (seq R M) (flipM R)`, `conj_partial_involution` for its semantics),
but discharging this single-tape `stringSem` form additionally needs (i)
the `Lift`/`Reindex` transport of the seq-machine back to `TM0` and (ii) a
`StdOutput` argument for the composite — both part of roadmap steps 2–3,
so this is left as a `Prop`, not an admitted proof. -/
def StringConjugationClosure : Prop :=
  ∀ (Γ ΛM ΛR : Type) [Inhabited Γ] [Inhabited ΛM] [Inhabited ΛR]
    (M : Machine Γ ΛM) (q₀ qf : ΛM)
    (R R' : Machine Γ ΛR) (r₀ r₀' : ΛR),
    SyntacticallyInvolutory M q₀ qf →
    StdOutput M q₀ →
    (∀ s t, t ∈ stringSem R r₀ s ↔ s ∈ stringSem R' r₀' t) →
    ∃ (Λ' : Type) (_ : Inhabited Λ') (D : Machine Γ Λ') (d₀ df : Λ'),
      SyntacticallyInvolutory D d₀ df ∧
      ∀ s, stringSem D d₀ s =
        (stringSem R r₀ s).bind fun u =>
          (stringSem M q₀ u).bind (stringSem R' r₀')

/-!
### Roadmap delta (step 1: string/IO-encoding bridge)

**Done here:**
* String-level notion `StringInvolutory` and the encoding-aware
  restatement `StringCompletenessGoal` (replacing strict `tapeSem`
  equality by `stringSem` agreement, as step 1 demanded).
* Soundness at string level: `SyntacticallyInvolutory.stringInvolutory`
  (closure (a)).
* The one-cell kernel fully lifted: `stringSem_writeHead` computes the
  induced string involution `applyHead g` totally, giving
  `completenessGoal_oneCell_string` and `stringInvolutory_writeHead`.
* Conjugation closure (b) proved semantically
  (`conj_stringPartialInvolution`) and stated syntactically
  (`StringConjugationClosure`).

**Remaining for step 1's consumers (steps 2–4):**
* Discharge `StringConjugationClosure` by transporting
  `conj_KInvolutory` / `conjSem` from the KMachine model to `TM0`
  (`Lift`/`Reindex`) and establishing `StdOutput` for the composite.
* `StdOutput` for the eventual 2k-tape symmetrisation (the main
  obligation flagged in `IOConvention.lean`), after which
  `SyntacticallyInvolutory.stringInvolutory` closes the soundness side
  of `StringCompletenessGoal` and steps 2–3 must supply the converse.
-/

end PeriodicTM
