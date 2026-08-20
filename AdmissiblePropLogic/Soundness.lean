import AdmissiblePropLogic.Semantics
import AdmissiblePropLogic.ProofSystem

set_option linter.style.header false
set_option linter.style.whitespace false
set_option linter.style.longLine false

namespace PropositionalLogic

-- ============================================================================
-- ## Consistency and completeness
-- ============================================================================

--
-- Soundness: `T ⊢ P` implies T ⊨ P (provability entails semantic truth),
-- and satisfiable theories are consistent.  The consistency lemmas below give the
-- (1)(2)(3) facts; the Soundness Theorem proves it by structural induction on the
-- derivation `T ⊢ P` — the `assm` constructor uses the `Satisfies` witness, each
-- axiom scheme is dispatched by its `tautology_*` fact from `ProofSystem`, and the
-- `mp` step chains the inductive hypotheses via `mp_preserves_truth`.
-- In plain terms: whatever this file claims, Lean means it, and it turns out to be true.

-- ----------------------------------------------------------------------------
-- Consistency and inconsistency
-- ----------------------------------------------------------------------------

-- Definition — Inconsistent / consistent
-- Let T ⊆ Prop. We say that T is **inconsistent** if T ⊢ ⊥; and T is **consistent** if T is not inconsistent.
-- A theory is inconsistent exactly when it proves the falsity constant `bot`;
-- consistent means it does not.  `Consistent` is the negation of `Inconsistent`.
def Inconsistent (T : Set Proposition) : Prop := T ⊢ bot
def Consistent (T : Set Proposition) : Prop := ¬ Inconsistent T

-- A consistent theory avoids contradiction
-- Let P be a proposition. If T is consistent, then T ⊬ P or T ⊬ ¬ P.
-- A theory consistent with respect to `P` cannot prove both `P` and its negation.
-- The shared engine is `inconsistent_of_both`: proving both collapses to `bot`
-- via the derived contradiction lemma `bot_of_contra` from `ProofSystem`.
-- One cannot have it both ways, and Lean does not let the theory try.

-- If a theory proves both `P` and `¬P`, it is inconsistent (it proves `bot`).
lemma inconsistent_of_both {T : Set Proposition} {P : Proposition}
    (hP : T ⊢ P) (hneg : T ⊢ neg P) : Inconsistent T := by
  unfold Inconsistent
  exact bot_of_contra hP hneg

-- A consistent theory leaves at least one of `P`, `¬P` unprovable.
theorem consistent_avoids_both {T : Set Proposition} {P : Proposition} (h : Consistent T) :
    (¬ (T ⊢ P)) ∨ (¬ (T ⊢ neg P)) := by
  classical
  by_cases hP : T ⊢ P
  · right
    intro hneg
    exact h (inconsistent_of_both hP hneg)
  · left
    exact hP

-- Provability vs inconsistency
-- Let P be a proposition. We have
-- (1) T ⊢ P if and only if T ∪ {¬ P} is inconsistent;
-- (2) if T is consistent and T ⊢ P, then T ∪ {P} is consistent; and
-- (3) if T is inconsistent, then there is a finite inconsistent subset T₀ of T.
-- (1): T ⊢ P iff T ∪ {¬ P} proves `bot`.  The (→) direction is the
-- explosion `inconsistent_of_both` on `P` and `¬P`.  The (←) direction is the
-- classical content: `T ∪ {¬P} ⊢ bot` gives `T ⊢ ¬P → bot` by the Deduction Lemma,
-- and the `raa` axiom (8) `(¬P→bot)→P` closes it.
-- The (←) half is classical through and through; `raa` is doing the worrying.
theorem provable_iff_inconsistent_neg {T : Set Proposition} {P : Proposition} :
    (T ⊢ P) ↔ Inconsistent (T ∪ ({neg P} : Set Proposition)) := by
  unfold Inconsistent
  constructor
  · intro hP
    let T' : Set Proposition := T ∪ ({neg P} : Set Proposition)
    exact inconsistent_of_both
      (weakening (by intro x hx; exact Or.inl hx) hP)
      (Ded.assm T' (neg P) (by simp [T']))
  · intro hbot
    have hded : T ⊢ implication (neg P) bot := deduction hbot
    exact Ded.mp T (implication (neg P) bot) P (Ded.raa T P) hded

-- (2): if `T` is consistent and proves `P`, then adding `P` keeps it consistent.
-- Contrapositive: `T ∪ {P} ⊢ bot` gives `T ⊢ P → bot` (Deduction Lemma), and MP
-- with `T ⊢ P` yields `T ⊢ bot`, contradicting consistency.
theorem inconsistent_add_of_provable {T : Set Proposition} {P : Proposition}
    (hcons : Consistent T) (hP : T ⊢ P) : Consistent (T ∪ ({P} : Set Proposition)) := by
  unfold Consistent
  intro hbot
  have hded : T ⊢ implication P bot := deduction hbot
  have hbot' : T ⊢ bot := Ded.mp T P bot hded hP
  exact hcons hbot'

-- (3): an inconsistent theory has a finite inconsistent subset.  This is exactly
-- the compactness theorem (`finite_subproof`), instantiated at the falsity constant `bot`.
theorem consistent_of_finite_consistent {T : Set Proposition} (h : Inconsistent T) :
    ∃ T₀ : Set Proposition, T₀.Finite ∧ T₀ ⊆ T ∧ Inconsistent T₀ := by
  unfold Inconsistent at h
  rcases finite_subproof h with ⟨T₀, hfin, hsub, hded⟩
  exact ⟨T₀, hfin, hsub, hded⟩

-- Double negation as a biconditional
-- For any proposition P, we have ⊢ ¬ ¬ P ↔ P.
-- The two implications that make up the biconditional `bicond (neg (neg P)) P`.
--   • `¬¬P → P` (double-negation elimination): under `¬¬P`, an assumed `¬P`
--     would be double trouble, so `¬P → bot`, and the `raa` axiom (8) finishes it.
--   • `P → ¬¬P` (double-negation introduction): the `deriv_neg_elim` (7) gives
--     `¬P → bot`, and `deriv_neg_intro` then hands back `¬¬P`.
-- `¬¬` is a reliable door that opens both ways; Lean verifies both trips.

-- ----------------------------------------------------------------------------
-- Double negation
-- ----------------------------------------------------------------------------

-- Double-negation elimination: `¬¬P` entails `P`.
theorem double_neg_elim (P : Proposition) :
    (∅ : Set Proposition) ⊢ implication (neg (neg P)) P := by
  have hAB : (∅ : Set Proposition) ⊢ implication (neg (neg P)) (implication (neg P) bot) :=
    imp_trans (deriv_double_neg_elim (P := P)) (deriv_neg_elim (P := P))
  have hBC : (∅ : Set Proposition) ⊢ implication (implication (neg P) bot) P :=
    Ded.raa (∅ : Set Proposition) P
  exact imp_trans hAB hBC

-- Double-negation introduction: `P` entails `¬¬P`.
theorem double_neg_intro (P : Proposition) :
    (∅ : Set Proposition) ⊢ implication P (neg (neg P)) := by
  have h1 : (∅ : Set Proposition) ⊢ implication P (implication (neg P) bot) :=
    deriv_neg_elim (P := P)
  have h2 : (∅ : Set Proposition) ⊢ implication (implication (neg P) bot) (neg (neg P)) :=
    deriv_neg_intro (P := neg P)
  exact imp_trans h1 h2

-- `⊢ not not P ↔ P`, glued as the biconditional
-- from the two implications above (the `deriv_conj_intro`-plus-two-MP pattern used for
-- the equivalence reflexivity).
theorem double_negation_tau (P : Proposition) :
    (∅ : Set Proposition) ⊢ bicond (neg (neg P)) P := by
  have h1 : (∅ : Set Proposition) ⊢ implication (neg (neg P)) P := double_neg_elim P
  have h2 : (∅ : Set Proposition) ⊢ implication P (neg (neg P)) := double_neg_intro P
  exact Ded.mp (∅ : Set Proposition) (implication P (neg (neg P))) (bicond (neg (neg P)) P)
    (Ded.mp (∅ : Set Proposition) (implication (neg (neg P)) P)
      (implication (implication P (neg (neg P))) (bicond (neg (neg P)) P))
      (deriv_conj_intro (P := implication (neg (neg P)) P) (Q := implication P (neg (neg P))))
      h1)
    h2

-- ----------------------------------------------------------------------------
-- Soundness
-- ----------------------------------------------------------------------------

-- Modus Ponens preserves truth
-- Let P, Q be propositions and t be a truth assignment. If t(P) = t(P → Q) = 1, then t(Q) = 1.
-- Modus Ponens is truth-preserving: if the premises `P` and `P → Q` are both true
-- under `t`, so is the conclusion `Q`.  `implication_true_iff` (from
-- `Semantics`) rewrites the true implication into the disjunction
-- `eval t P = false ∨ eval t Q = true`; the first disjunct contradicts `hP`.
-- Truth in, truth out; it is the system's only rule, and it obeys itself.
theorem mp_preserves_truth {t : TruthAssignment} {P Q : Proposition}
    (hP : eval t P = true) (hI : eval t (implication P Q) = true) : eval t Q = true := by
  have hiff : eval t (implication P Q) = true ↔ eval t P = false ∨ eval t Q = true :=
    implication_true_iff
  rw [hiff] at hI
  rcases hI with hPf | hQe
  · rw [hP] at hPf
    simp at hPf
  · exact hQe

-- Soundness Theorem
-- (1) For any proposition P if T ⊢ P, then T ⊨ P.
-- (2) If T is satisfiable, then T is consistent.
-- (1) — Soundness.  Structural induction on the derivation `h : T ⊢ P`.
--   • `assm`: the premise `P ∈ T` feeds the `Satisfies` witness directly.
--   • axiom schemes: the scheme is a `Tautology` (the `tautology_*` theorems of
--     `ProofSystem`), so its evaluation is `true` and the `Satisfies` premise is unused.
--   • `mp`: the IHs give entailments of `A → B` and `A`; the Modus-Ponens-preserves-truth lemma chains them.
-- Provability never outruns truth. This is the point of the whole project, stated
-- quietly so as not to alarm the logic, the machine, or the reader.
theorem soundness {T : Set Proposition} {P : Proposition} (h : T ⊢ P) : Entails T P := by
  induction h with
  | assm Q hmem =>
      intro t ht
      exact ht Q hmem
  | imp_1 A B =>
      intro t ht
      exact tautology_imp_1 t
  | imp_2 A B C =>
      intro t ht
      exact tautology_imp_2 t
  | neg_contra A B =>
      intro t ht
      exact tautology_neg_contra t
  | raa A =>
      intro t ht
      exact tautology_raa t
  | mp A B hf hp ihf ihp =>
      intro t ht
      exact mp_preserves_truth (ihp t ht) (ihf t ht)

-- (2) — a satisfiable theory is consistent.  If it proved `bot`, Soundness would
-- force `eval t bot = true` for any satisfying assignment `t`, contradicting
-- `eval_bot` (which evaluates `bot` to `false`).
theorem consistent_of_satisfiable {T : Set Proposition} (h : Satisfiable T) : Consistent T := by
  unfold Consistent Inconsistent
  intro hbot
  rcases h with ⟨t, ht⟩
  have hent : Entails T bot := soundness hbot
  have hb : eval t bot = true := hent t ht
  have hfb : eval t bot = false := by simp [eval_bot]
  rw [hfb] at hb
  simp at hb

-- Contrapositive of Soundness: a proposition that is *not* entailed is not provable.
-- This is the workhorse behind every *non-provability* claim in this project
-- (e.g. the claim example "∅ and {P₀} are not complete"): to refute `T ⊢ P`, exhibit
-- a truth assignment satisfying `T` under which `P` is false.
-- To refute is to produce a counterexample; Lean forgives the transgression
-- because it is able to check it in full.
theorem not_ded_of_not_entails {T : Set Proposition} {P : Proposition}
    (h : ¬ Entails T P) : ¬ (T ⊢ P) := by
  intro hded
  exact h (soundness hded)

-- ----------------------------------------------------------------------------
-- Axioms are tautologies
-- ----------------------------------------------------------------------------

-- Axioms are tautologies
-- Every propositional axiom is a tautology.  The `tautology_*` theorems in
-- `ProofSystem.lean` — one per axiom scheme of the `Ded` system, cited by
-- `soundness` — are still around, though only the six primitive schemes
-- (`imp_1`, `imp_2`, `neg_contra`, `raa`, `mp`, plus `assm`) drive the
-- induction; the connective schemes have become derived theorems.
-- Notable survivors:
--   `tautology_imp₁`            —  (2) `P → (Q → P)`
--   `tautology_imp₂`            —  (6) `(P→(Q→R))→((P→Q)→(P→R))`
--   `tautology_neg_contra`       —  contraposition scheme `(¬P→¬Q)→(Q→P)`
--   `tautology_raa`              —  (8) `(¬P→⊥)→P`

end PropositionalLogic