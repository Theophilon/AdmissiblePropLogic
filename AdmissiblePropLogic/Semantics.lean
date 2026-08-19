import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Basic
import AdmissiblePropLogic.AdmissibleWord
import AdmissiblePropLogic.Proposition

set_option linter.style.header false
set_option linter.style.whitespace false
set_option linter.style.longLine false

namespace PropositionalLogic

open Admissibility

-- ============================================================================
-- ## Truth semantics
-- ============================================================================

-- ----------------------------------------------------------------------------
-- Truth assignments and evaluation
-- ----------------------------------------------------------------------------

-- Truth assignment: a truth value for every propositional variable.
-- `abbrev` so that a function literal `fun _ => true` elaborates directly.
-- Some traditions call this a model; we call it a function and get on with it.
abbrev TruthAssignment : Type := ℕ → Bool

-- Evaluation of a proposition under a truth assignment.
-- The intrinsic `AdmissibleWord` type makes this a plain structural recursion:
-- a `Proposition` is well-formed by construction, so `eval` needs no admissibility
-- witness and no totality argument. A machine wrote the grammar; Lean only has
-- to confirm that the resulting recursion is as complete as it claims.
def eval (t : TruthAssignment) : Proposition → Bool
  | .atom s _ =>
      match s with
      | LogicalSymbol.var v => t v
      | LogicalSymbol.top   => true
      | LogicalSymbol.bot   => false
      | _ => false
  | .app s ha args =>
      match s with
      | LogicalSymbol.neg  => !(eval t (args ⟨0, ha⟩))
      | LogicalSymbol.conj => eval t (args ⟨0, ha⟩) && eval t (args ⟨1, by decide⟩)
      | LogicalSymbol.disj => eval t (args ⟨0, ha⟩) || eval t (args ⟨1, by decide⟩)
      | _ => false

-- ----------------------------------------------------------------------------
-- Connectives and their evaluation
-- ----------------------------------------------------------------------------

-- Component evaluation rules: each connective reduces `eval` to the corresponding
-- Bool primitive.  These are the [simp] targets throughout the section; Lean
-- applies them with far more patience than any human reader cares to.
lemma eval_neg {t : TruthAssignment} {P : Proposition} : eval t (neg P) = !(eval t P) := by
  simp [eval, neg]
lemma eval_conj {t : TruthAssignment} {P Q : Proposition} :
    eval t (conj P Q) = (eval t P && eval t Q) := by
  simp [eval, conj]
lemma eval_disj {t : TruthAssignment} {P Q : Proposition} :
    eval t (disj P Q) = (eval t P || eval t Q) := by
  simp [eval, disj]
lemma eval_var {t : TruthAssignment} {n : ℕ} : eval t (var n) = t n := by
  simp [eval, var]
lemma eval_top (t : TruthAssignment) : eval t top = true := by
  simp [eval, top]
lemma eval_bot (t : TruthAssignment) : eval t bot = false := by
  simp [eval, bot]

-- Connective abbreviations. Implication is *defined*, not derived from a nicer
-- intuition: P → Q := ¬ P ∨ Q;  P ⇔ Q := (P → Q) ∧(Q → P). It is what the
-- material reading of `→` leaves you with, and the material reading won.
def implication (P Q : Proposition) : Proposition := disj (neg P) Q
def bicond (P Q : Proposition) : Proposition := conj (implication P Q) (implication Q P)

-- Evaluation of the abbreviation `→`: unfolds to `¬P ∨ Q`, i.e. the
-- material implication truth table t(P) ≤ t(Q).
lemma eval_implication {t : TruthAssignment} {P Q : Proposition} :
    eval t (implication P Q) = (!(eval t P) || eval t Q) := by
  simp [implication, eval_disj, eval_neg]

-- Evaluation of the abbreviation `↔`: both implications, i.e. t(P) = t(Q).
lemma eval_bicond {t : TruthAssignment} {P Q : Proposition} :
    eval t (bicond P Q) = ((!(eval t P) || eval t Q) && (!(eval t Q) || eval t P)) := by
  simp [bicond, eval_conj, eval_implication]

-- Ex (1): P → Q is true iff t(P) ≤ t(Q)
-- (in Bool, `eval t P = false ∨ eval t Q = true`).
theorem implication_true_iff {t : TruthAssignment} {P Q : Proposition} :
    eval t (implication P Q) = true ↔ eval t P = false ∨ eval t Q = true := by
  rw [eval_implication]
  cases eval t P <;> cases eval t Q <;> simp

-- Ex (2): P ↔ Q is true iff t(P) = t(Q).
theorem bicond_true_iff {t : TruthAssignment} {P Q : Proposition} :
    eval t (bicond P Q) = true ↔ eval t P = eval t Q := by
  rw [eval_bicond]
  cases eval t P <;> cases eval t Q <;> simp

-- Tautology / contradiction.
def Tautology (P : Proposition) : Prop := ∀ t : TruthAssignment, eval t P = true
def Contradiction (P : Proposition) : Prop := ∀ t : TruthAssignment, eval t P = false

-- Equivalence: P ↔ Q is a tautology (i.e. t(P)=t(Q) for all t).
def Equivalent (P Q : Proposition) : Prop := ∀ t : TruthAssignment, eval t P = eval t Q

-- Bool identities used to close the truth-functional goals below. By the time a
-- goal has been reduced to a finite table of truth values, the hard part is over.
lemma bool_or_not (b : Bool) : ((!b) || b) = true := by cases b <;> decide
lemma bool_and_not (b : Bool) : (b && (!b)) = false := by cases b <;> decide
lemma bool_and_comm (a b : Bool) : (a && b) = (b && a) := by cases a <;> cases b <;> decide
lemma bool_or_comm (a b : Bool) : (a || b) = (b || a) := by cases a <;> cases b <;> decide
lemma bool_and_assoc (a b c : Bool) : ((a && b) && c) = (a && (b && c)) := by
  cases a <;> cases b <;> cases c <;> decide
lemma bool_or_assoc (a b c : Bool) : ((a || b) || c) = (a || (b || c)) := by
  cases a <;> cases b <;> cases c <;> decide
lemma bool_and_or_distrib (a b c : Bool) : (a && (b || c)) = ((a && b) || (a && c)) := by
  cases a <;> cases b <;> cases c <;> decide
lemma bool_or_and_distrib (a b c : Bool) : (a || (b && c)) = ((a || b) && (a || c)) := by
  cases a <;> cases b <;> cases c <;> decide
lemma bool_not_and (a b : Bool) : (!(a && b)) = ((!a) || (!b)) := by
  cases a <;> cases b <;> decide
lemma bool_not_or (a b : Bool) : (!(a || b)) = ((!a) && (!b)) := by
  cases a <;> cases b <;> decide
lemma bool_not_not (b : Bool) : !(!b) = b := by cases b <;> decide

-- (remarks) + tests: truth value under t. QED by `simp`, as is right and proper.
example : eval (fun _ => true) (var 3) = true := by simp [eval, var]
example : eval (fun _ => true) (neg (var 3)) = false := by simp [eval, neg, var]
example : eval (fun n => decide (n = 0)) (disj (var 0) (bot)) = true := by
  simp [eval, disj, var, bot]
example : eval (fun n => decide (n = 1)) (conj (var 0) (var 1)) = false := by
  simp [eval, conj, var]

-- Example — ⊤ and P₀ → P₀ tautologies; ⊥ and P₀ ∧ ¬ P₀ contradictions.
-- Truth and its absence, conveniently located, each machine-checked.
theorem tautology_top : Tautology top := by intro t; simp [eval, top]
theorem tautology_imp_self : Tautology (implication (var 0) (var 0)) := by
  intro t
  simp [eval_implication, eval_var]
theorem contradiction_bot : Contradiction bot := by intro t; simp [eval, bot]
theorem contradiction_conj_neg : Contradiction (conj (var 0) (neg (var 0))) := by
  intro t
  simp [eval_conj, eval_neg, eval_var]

-- ----------------------------------------------------------------------------
-- Satisfiability and entailment
-- ----------------------------------------------------------------------------

-- Satisfies / Satisfiable / Entails.
-- t satisfies T if every proposition in T is true under t; T is satisfiable if
-- some assignment satisfies it; T entails P (written T ⊨ P) if every
-- assignment satisfying T also satisfies {P}. The turnstile looks authoritative;
-- it is, in the end, an abbreviation with a strict upbringing.
def Satisfies (t : TruthAssignment) (T : Set Proposition) : Prop := ∀ P, P ∈ T → eval t P = true
def Satisfiable (T : Set Proposition) : Prop := ∃ t : TruthAssignment, Satisfies t T
def Entails (T : Set Proposition) (P : Proposition) : Prop :=
  ∀ t : TruthAssignment, Satisfies t T → eval t P = true

-- Example — ∅ and {P₀} are satisfiable; the full set and {P₀, ¬ P₀} are not.
theorem empty_satisfiable : Satisfiable (∅ : Set Proposition) := by
  use (fun _ => true)
  rintro P hP
  simp at hP

-- Example — {P₀} is satisfiable: the all-true assignment
-- makes the single variable `P₀` true.
theorem singleton_satisfiable : Satisfiable ({var 0} : Set Proposition) := by
  use (fun _ => true)
  rintro P hP
  have hPeq : P = var 0 := by simpa using hP
  subst P
  simp [eval_var]

-- Example — the full set of all propositions is not satisfiable: it
-- contains `bot`, and no assignment makes `bot` true. The full universe of
-- propositions is thus the one set that fails on its own terms.
theorem univ_not_satisfiable : ¬ Satisfiable (Set.univ : Set Proposition) := by
  rintro ⟨t, ht⟩
  have htbot : eval t bot = true := ht bot (by simp)
  have hfb : eval t bot = false := by simp [eval_bot]
  rw [hfb] at htbot
  simp at htbot

-- Example — {P₀, ¬P₀} is not satisfiable: one assignment cannot make
-- both a variable and its negation true.
theorem var_neg_not_satisfiable : ¬ Satisfiable ({var 0, neg (var 0)} : Set Proposition) := by
  rintro ⟨t, ht⟩
  have h0 : eval t (var 0) = true := ht (var 0) (by simp)
  have hn : eval t (neg (var 0)) = true := ht (neg (var 0)) (by simp)
  have : eval t (var 0) = false := by simpa [eval_neg, Bool.not_eq_true] using hn
  rw [h0] at this
  simp at this

-- Example — {P₀ ∨ P₁, P₁ → ¬ P₂, P₂} is satisfiable.
theorem satisfiable_example_set :
    Satisfiable ({disj (var 0) (var 1), implication (var 1) (neg (var 2)), var 2}
      : Set Proposition) := by
  let t : TruthAssignment := fun n => if n = 2 then true else if n = 1 then false else true
  refine ⟨t, ?_⟩
  rintro P hP
  have hmem : P = disj (var 0) (var 1) ∨ P = implication (var 1) (neg (var 2)) ∨ P = var 2 := by
    simpa using hP
  rcases hmem with rfl | rfl | rfl
  · decide
  · decide
  · decide

-- ----------------------------------------------------------------------------
-- Dependence on the variables used
-- ----------------------------------------------------------------------------

-- Variables occurring in a proposition, harvested by structural recursion.
-- Wherever the recursion goes, the set cannot help but follow.
def UsedVars : Proposition → Set ℕ
  | .atom (.var n) _ => {n}
  | .atom _ _ => ∅
  | .app .neg _ args => UsedVars (args ⟨0, by decide⟩)
  | .app .conj _ args => UsedVars (args ⟨0, by decide⟩) ∪ UsedVars (args ⟨1, by decide⟩)
  | .app .disj _ args => UsedVars (args ⟨0, by decide⟩) ∪ UsedVars (args ⟨1, by decide⟩)
  | .app _ _ _ => ∅

-- Evaluation depends only on the variables occurring in the proposition.
-- If t₁,t₂ agree on every variable of P then t₁(P) = t₂(P). Variables
-- the proposition has never heard of do not weigh on the outcome.
theorem eval_agrees_on_vars {t₁ t₂ : TruthAssignment} (P : Proposition)
    (h : ∀ n : ℕ, n ∈ UsedVars P → t₁ n = t₂ n) : eval t₁ P = eval t₂ P := by
  revert h
  induction P with
  | atom a ha =>
      intro h
      cases a with
      | var n =>
          have : t₁ n = t₂ n := h n (by simp [UsedVars])
          simpa [eval] using this
      | top => simp [eval]
      | bot => simp [eval]
      | neg => simp [Arity.arity] at ha
      | conj => simp [Arity.arity] at ha
      | disj => simp [Arity.arity] at ha
  | app a ha args ih =>
      intro h
      cases a with
      | var n => simp [Arity.arity] at ha
      | top => simp [Arity.arity] at ha
      | bot => simp [Arity.arity] at ha
      | neg =>
          have harg : ∀ n, n ∈ UsedVars (args ⟨0, ha⟩) → t₁ n = t₂ n := by
            intro n hn
            exact h n (by simpa [UsedVars] using hn)
          have hh : eval t₁ (args ⟨0, ha⟩) = eval t₂ (args ⟨0, ha⟩) := ih ⟨0, ha⟩ harg
          simpa [eval, hh]
      | conj =>
          have harg0 : ∀ n, n ∈ UsedVars (args ⟨0, ha⟩) → t₁ n = t₂ n := by
            intro n hn; exact h n (by simpa [UsedVars] using Or.inl hn)
          have harg1 : ∀ n, n ∈ UsedVars (args ⟨1, by decide⟩) → t₁ n = t₂ n := by
            intro n hn; exact h n (by simpa [UsedVars] using Or.inr hn)
          have h0 : eval t₁ (args ⟨0, ha⟩) = eval t₂ (args ⟨0, ha⟩) := ih ⟨0, ha⟩ harg0
          have h1 : eval t₁ (args ⟨1, by decide⟩) = eval t₂ (args ⟨1, by decide⟩) := ih ⟨1, by decide⟩ harg1
          change (eval t₁ (args ⟨0, ha⟩) && eval t₁ (args ⟨1, by decide⟩)) =
                 (eval t₂ (args ⟨0, ha⟩) && eval t₂ (args ⟨1, by decide⟩))
          rw [h0, h1]
      | disj =>
          have harg0 : ∀ n, n ∈ UsedVars (args ⟨0, ha⟩) → t₁ n = t₂ n := by
            intro n hn; exact h n (by simpa [UsedVars] using Or.inl hn)
          have harg1 : ∀ n, n ∈ UsedVars (args ⟨1, by decide⟩) → t₁ n = t₂ n := by
            intro n hn; exact h n (by simpa [UsedVars] using Or.inr hn)
          have h0 : eval t₁ (args ⟨0, ha⟩) = eval t₂ (args ⟨0, ha⟩) := ih ⟨0, ha⟩ harg0
          have h1 : eval t₁ (args ⟨1, by decide⟩) = eval t₂ (args ⟨1, by decide⟩) := ih ⟨1, by decide⟩ harg1
          change (eval t₁ (args ⟨0, ha⟩) || eval t₁ (args ⟨1, by decide⟩)) =
                 (eval t₂ (args ⟨0, ha⟩) || eval t₂ (args ⟨1, by decide⟩))
          rw [h0, h1]

-- ----------------------------------------------------------------------------
-- Equivalence and its laws
-- ----------------------------------------------------------------------------

-- Ex — ⇔ (Equivalent) is an equivalence relation on propositions. Reflexive,
-- symmetric, transitive; the least one can ask of a symbol that looks like a
-- two-headed arrow.
theorem equivalent_refl (P : Proposition) : Equivalent P P := fun _ => rfl
theorem equivalent_symm {P Q : Proposition} (h : Equivalent P Q) : Equivalent Q P :=
  fun t => (h t).symm
theorem equivalent_trans {P Q R : Proposition} (h₁ : Equivalent P Q) (h₂ : Equivalent Q R) :
    Equivalent P R := fun t => (h₁ t).trans (h₂ t)

-- The twelve laws of propositional equivalence, machine-declared and
-- Lean-endorsed in one undignified ceremony.
-- (1) ¬ ¬ P ⇔ P.
theorem equivalent_dneg (P : Proposition) : Equivalent (neg (neg P)) P := by
  intro t; simp [eval_neg]
-- (2) P ∨ ¬ P ⇔ ⊤.
theorem equivalent_or_not (P : Proposition) : Equivalent (disj P (neg P)) top := by
  intro t; simp [eval_disj, eval_neg, eval_top]
-- (3) P ∧ Q ⇔ Q ∧ P, P ∨ Q ⇔ Q ∨ P.
theorem equivalent_conj_comm (P Q : Proposition) : Equivalent (conj P Q) (conj Q P) := by
  intro t; simp [eval_conj, bool_and_comm]
theorem equivalent_disj_comm (P Q : Proposition) : Equivalent (disj P Q) (disj Q P) := by
  intro t; simp [eval_disj, bool_or_comm]
-- (4) associativity.
theorem equivalent_conj_assoc (P Q R : Proposition) :
    Equivalent (conj (conj P Q) R) (conj P (conj Q R)) := by
  intro t; simp [eval_conj, bool_and_assoc]
theorem equivalent_disj_assoc (P Q R : Proposition) :
    Equivalent (disj (disj P Q) R) (disj P (disj Q R)) := by
  intro t; simp [eval_disj, bool_or_assoc]
-- (5) distributivity.
theorem equivalent_conj_distrib (P Q R : Proposition) :
    Equivalent (conj P (disj Q R)) (disj (conj P Q) (conj P R)) := by
  intro t; simp [eval_conj, eval_disj, bool_and_or_distrib]
theorem equivalent_disj_distrib (P Q R : Proposition) :
    Equivalent (disj P (conj Q R)) (conj (disj P Q) (disj P R)) := by
  intro t; simp [eval_disj, eval_conj, bool_or_and_distrib]
-- (6) P → Q ⇔ ¬ Q → ¬ P (contraposition).
theorem equivalent_contraposition (P Q : Proposition) :
    Equivalent (implication P Q) (implication (neg Q) (neg P)) := by
  intro t
  simp [eval_implication, eval_neg, bool_or_comm]
-- (7) De Morgan / constants.
theorem equivalent_not_top : Equivalent (neg top) bot := by
  intro t; simp [eval_neg, eval_top, eval_bot]
theorem equivalent_not_conj (P Q : Proposition) :
    Equivalent (neg (conj P Q)) (disj (neg P) (neg Q)) := by
  intro t; simp [eval_neg, eval_conj, eval_disj]
theorem equivalent_not_disj (P Q : Proposition) :
    Equivalent (neg (disj P Q)) (conj (neg P) (neg Q)) := by
  intro t; simp [eval_neg, eval_conj, eval_disj]

-- ----------------------------------------------------------------------------
-- Classifying concrete propositions
-- ----------------------------------------------------------------------------

-- Exercise (for testing the tautology / contradiction definition). Classify each
-- proposition. The predicates have opinions; the theorems only record them.
def proposition_a : Proposition := implication (implication (implication (var 0) (var 0)) (var 0)) (var 0)
def proposition_b : Proposition := implication (implication (implication (var 0) (var 0)) (var 1)) (var 0)
def proposition_c : Proposition := conj (implication (var 1) (var 2)) (implication (var 1) (neg (var 2)))

-- (1) ((P₀ → P₀) → P₀) → P₀ -- a tautology.
theorem proposition_a_tautology : Tautology proposition_a := by
  intro t
  cases h0 : t 0 <;> simp [proposition_a, eval_implication, eval_var, h0]

-- (2) ((P₀ → P₀) → P₁) → P₀ -- neither.
-- P₀ := false, P₁ := true gives false.
theorem proposition_b_not_tautology : ¬ Tautology proposition_b := by
  intro h
  let t : TruthAssignment := fun n => if n = 0 then false else if n = 1 then true else false
  have hf : eval t proposition_b = false := by decide
  have ht := h t
  rw [hf] at ht
  simp at ht
-- P₀ := true gives true.
theorem proposition_b_not_contradiction : ¬ Contradiction proposition_b := by
  intro h
  let t : TruthAssignment := fun n => if n = 0 then true else false
  have ht : eval t proposition_b = true := by decide
  have hf := h t
  rw [ht] at hf
  simp at hf

-- (3) (P₁ → P₂) ∧ (P₁ → ¬ P₂) -- neither.
-- P₁ := true, P₂ := true gives false.
theorem proposition_c_not_tautology : ¬ Tautology proposition_c := by
  intro h
  let t : TruthAssignment := fun _ => true
  have hf : eval t proposition_c = false := by decide
  have ht := h t
  rw [hf] at ht
  simp at ht
-- P₁ := false gives true.
theorem proposition_c_not_contradiction : ¬ Contradiction proposition_c := by
  intro h
  let t : TruthAssignment := fun n => if n = 1 then false else true
  have ht : eval t proposition_c = true := by decide
  have hf := h t
  rw [ht] at hf
  simp at hf

-- ----------------------------------------------------------------------------
-- Entailment from inconsistent theories
-- ----------------------------------------------------------------------------

-- Ex — P is a tautology iff ⊨ P (empty theory entails P).
theorem tautology_iff_entails_empty (P : Proposition) : Tautology P ↔ Entails (∅ : Set Proposition) P := by
  simp [Tautology, Entails, Satisfies]

-- Ex — {P ∨ Q, ¬ R → ¬ Q, ¬ P} ⊨ R.
theorem entails_disjunction_neg_chain {P Q R : Proposition} :
    Entails ({disj P Q, implication (neg R) (neg Q), neg P} : Set Proposition) R := by
  intro t ht
  have h3 : eval t (neg P) = true := ht (neg P) (by simp)
  have hPe : eval t P = false := by simpa [eval_neg, Bool.not_eq_true] using h3
  have hQe : eval t Q = true := by
    have h1 : eval t (disj P Q) = true := ht (disj P Q) (by simp)
    have : eval t P || eval t Q = true := by simpa [eval_disj] using h1
    simpa [hPe] using this
  have hRe : eval t R = true := by
    have h2 : eval t (implication (neg R) (neg Q)) = true :=
      ht (implication (neg R) (neg Q)) (by simp)
    have : (eval t R || !(eval t Q)) = true := by simpa [eval_implication, eval_neg, bool_not_not] using h2
    simpa [hQe] using this
  exact hRe

-- Ex — {P₀, ¬ P₀} ⊨ P for every proposition P (ex falso from inconsistency).
-- From a contradiction everything follows, including statements the author
-- would not have volunteered if the turnstile had given them a choice.
theorem entails_from_inconsistent (P : Proposition) :
    Entails ({var 0, neg (var 0)} : Set Proposition) P := by
  intro t ht
  have h0 : eval t (var 0) = true := ht (var 0) (by simp)
  have hn : eval t (neg (var 0)) = true := ht (neg (var 0)) (by simp)
  have : eval t (var 0) = false := by simpa [eval_neg, Bool.not_eq_true] using hn
  exfalso
  rw [h0] at this
  simp at this

end PropositionalLogic