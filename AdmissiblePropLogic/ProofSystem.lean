import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Basic
import AdmissiblePropLogic.AdmissibleWord
import AdmissiblePropLogic.Proposition
import AdmissiblePropLogic.Semantics

set_option linter.style.header false
set_option linter.style.whitespace false
set_option linter.style.longLine false

namespace PropositionalLogic

-- ============================================================================
-- ## Formal proofs
-- ============================================================================

-- Definition — Propositional axiom
-- ----------------------------------------------------------------------------
-- The propositional axiom schemes
-- ----------------------------------------------------------------------------

-- A **propositional axiom** is a proposition that occurs in the list below, for some choice of P, Q and R;
-- (1) ⊤;
-- (2) P → (P ∨ Q); P → (Q ∨ P); P → (Q → P);
-- (3) ¬ P → (¬ Q → ¬ (P ∨ Q));
-- (4) (P ∧ Q) → P; (P ∧ Q) → Q;
-- (5) P → (Q → (P ∧ Q));
-- (6) (P → (Q → R)) → ((P → Q) → (P → R));
-- (7) P → (¬ P → ⊥);
-- (8) (¬ P → ⊥) → P.

-- The implication arrow → is NOT a new `LogicalSymbol`: it is the abbreviation
-- `implication` already defined in Semantics as ¬ P ∨ Q. Every axiom
-- scheme below is therefore stated over the real letters `neg`/`conj`/`disj` only.
-- Reassuring, in a small way: the machine will not accept a connective smuggled in
-- through a comment. It has to be declared honestly in the code before it may be used.

-- Propositional axioms are tautologies
-- Prove that all propositional axioms are tautologies.
-- ----------------------------------------------------------------------------
-- Axioms are tautologies
-- ----------------------------------------------------------------------------

-- All thirteen axiom schemes of the `Ded` system below are tautologies (soundness of
-- the single axiom/rule presentation). Each is `Tautology`, i.e. true under every
-- truth assignment: expand the abbreviation layers with the `eval_*` lemmas, then the
-- goal is a closed truth-functional `Bool` identity closed by `decide`.
-- `decide` does not care how the goal was phrased; it only checks it. A useful
-- temperament, and one to keep in mind while reading on.

-- (1) `top`
theorem tautology_top_axiom : Tautology top := by
  intro t
  simp [eval_top]
-- (2a) P → (P ∨ Q)
theorem tautology_disj_intro_left {P Q : Proposition} :
    Tautology (implication P (disj P Q)) := by
  intro t
  simp only [eval_implication, eval_disj]
  cases eval t P <;> cases eval t Q <;> decide
-- (2b) P → (Q ∨ P)
theorem tautology_disj_intro_right {P Q : Proposition} :
    Tautology (implication P (disj Q P)) := by
  intro t
  simp only [eval_implication, eval_disj]
  cases eval t P <;> cases eval t Q <;> decide
-- (2c) P → (Q → P)
theorem tautology_imp_1 {P Q : Proposition} :
    Tautology (implication P (implication Q P)) := by
  intro t
  simp only [eval_implication]
  cases eval t P <;> cases eval t Q <;> decide
-- (6) (P → (Q → R)) → ((P → Q) → (P → R))
theorem tautology_imp_2 {P Q R : Proposition} :
    Tautology (implication (implication P (implication Q R))
                            (implication (implication P Q) (implication P R))) := by
  intro t
  simp only [eval_implication]
  cases eval t P <;> cases eval t Q <;> cases eval t R <;> decide
-- contraposition scheme used by `Ded.neg_contra`: (¬ P → ¬ Q) → (Q → P)
theorem tautology_neg_contra {P Q : Proposition} :
    Tautology (implication (implication (neg P) (neg Q)) (implication Q P)) := by
  intro t
  simp only [eval_implication, eval_neg]
  cases eval t P <;> cases eval t Q <;> decide
-- ex-falso / efq scheme: ⊥ → P
theorem tautology_efq {P : Proposition} : Tautology (implication bot P) := by
  intro t
  simp [eval_implication, eval_bot]
-- (7) P → (¬ P → ⊥) — contradiction/explosion scheme: together,
-- `P` and `¬P` force `bot`.
theorem tautology_neg_elim {P : Proposition} :
    Tautology (implication P (implication (neg P) bot)) := by
  intro t
  simp only [eval_implication, eval_neg, eval_bot]
  cases eval t P <;> decide
-- (8) (¬ P → ⊥) → P — reductio ad absurdum (RAA): if `¬P`
-- entails `bot`, then `P` holds.  This is the classical axiom whose absence made
-- the old `Ded` system not classically complete.
theorem tautology_raa {P : Proposition} :
    Tautology (implication (implication (neg P) bot) P) := by
  intro t
  simp only [eval_implication, eval_neg, eval_bot]
  cases eval t P <;> decide
-- (4a) (P ∧ Q) → P
theorem tautology_conj_elim_left {P Q : Proposition} :
    Tautology (implication (conj P Q) P) := by
  intro t
  simp only [eval_implication, eval_conj]
  cases eval t P <;> cases eval t Q <;> decide
-- (4b) (P ∧ Q) → Q
theorem tautology_conj_elim_right {P Q : Proposition} :
    Tautology (implication (conj P Q) Q) := by
  intro t
  simp only [eval_implication, eval_conj]
  cases eval t P <;> cases eval t Q <;> decide
-- (5) P → (Q → (P ∧ Q))
theorem tautology_conj_intro {P Q : Proposition} :
    Tautology (implication P (implication Q (conj P Q))) := by
  intro t
  simp only [eval_implication, eval_conj]
  cases eval t P <;> cases eval t Q <;> decide
-- disjunction-elimination scheme: (P → R) → ((Q → R) → ((P ∨ Q) → R))
theorem tautology_disj_elim {P Q R : Proposition} :
    Tautology (implication (implication P R)
              (implication (implication Q R) (implication (disj P Q) R))) := by
  intro t
  simp only [eval_implication, eval_disj]
  cases eval t P <;> cases eval t Q <;> cases eval t R <;> decide

-- ----------------------------------------------------------------------------
-- Modus Ponens and the Ded relation
-- ----------------------------------------------------------------------------

-- Definition — Modus Ponens
-- **Modus Ponens (MP)** is the only rule of inference for propositional logic:
-- 
-- *From P and P → Q, infer Q.*

-- Definition — Formal proof / provable (stated for completeness of exposition; the working definition is the experiment encoding below, which this one is clanky to manipulate)
-- Let T ⊆ Prop and P ∈ Prop. A **formal proof** of P from T is a sequence Q₁, ..., Qₙ such that Qₙ = P and for every k ∈ {1, ..., n},
-- (1) Qₖ ∈ T;
-- (2) Qₖ is a propositional axiom; or
-- (3) Qₖ can be inferred from Qᵢ and Qⱼ by MP for some Qᵢ, Qⱼ ∈ {Q₁, ..., Qₖ₋₁}.
-- 
-- We say that **T proves P** (or P is **provable** from T) and denoted by T ⊢ P if there exists a formal proof of P from T. If T doesn't prove P, we denote by T ⊬ P.

-- ----------------------------------------------------------------------------
-- The provability relation Ded
-- ----------------------------------------------------------------------------

-- Experiment encoding. Instead of a clunky sequence of
-- propositions, provability is one inductive family indexed by (context, conclusion). Each
-- axiom scheme is a constructor, and Modus Ponens
-- is the single `mp` rule. The arrow in every scheme is the `Semantics.implication`
-- abbreviation, so constructors mention only the real letters `neg`/`conj`/`disj`/`top`/`bot`.
--
-- Attribution / inspiration: the key design choice here is that `Ded` is an *inductive
-- family* — an indexed type where each constructor is a proof-building rule and an
-- inhabitant IS a derivation (there is no standalone "proof" type). That representation
-- follows the provability relations in `guodk/PropLogicLean` (Lean4, completeness for
-- propositional logic) and `m4lvin/lean4-pdl` (PDL in Lean4).
-- Because a derivation *is* its inhabitant, there is no separate proof object where
-- a mistake could sit quietly; and even so, Lean would have noticed it anyway.
inductive Ded : Set Proposition → Proposition → Prop
  | assm         : ∀ Γ P, P ∈ Γ → Ded Γ P
  | imp_1        : ∀ Γ P Q, Ded Γ (implication P (implication Q P))
  | imp_2        : ∀ Γ P Q R,
      Ded Γ (implication (implication P (implication Q R))
                          (implication (implication P Q) (implication P R)))
  | neg_contra   : ∀ Γ P Q, Ded Γ (implication (implication (neg P) (neg Q)) (implication Q P))
  | neg_elim     : ∀ Γ P, Ded Γ (implication P (implication (neg P) bot))
  | raa          : ∀ Γ P, Ded Γ (implication (implication (neg P) bot) P)
  | efq          : ∀ Γ P, Ded Γ (implication bot P)
  | top_intro    : ∀ Γ, Ded Γ top
  | conj_elim_left  : ∀ Γ P Q, Ded Γ (implication (conj P Q) P)
  | conj_elim_right : ∀ Γ P Q, Ded Γ (implication (conj P Q) Q)
  | conj_intro      : ∀ Γ P Q, Ded Γ (implication P (implication Q (conj P Q)))
  | disj_intro_left  : ∀ Γ P Q, Ded Γ (implication P (disj P Q))
  | disj_intro_right : ∀ Γ P Q, Ded Γ (implication Q (disj P Q))
  | disj_elim        : ∀ Γ P Q R,
      Ded Γ (implication (implication P R)
            (implication (implication Q R) (implication (disj P Q) R)))
  | mp : ∀ Γ P Q, Ded Γ (implication P Q) → Ded Γ P → Ded Γ Q

notation : 45 Γ "⊢" φ => Ded Γ φ

-- A hypothesis is provable (trivial under our experiment definition).
-- Let T ⊆ Prop and P ∈ Prop. Prove that if P ∈ T, then T ⊢ P.
-- A hypothesis of the context is immediately provable (the `assm` constructor).
theorem provable_of_mem {Γ : Set Proposition} {P : Proposition} (h : P ∈ Γ) : Γ ⊢ P :=
  Ded.assm Γ P h

-- Definition — Modus Ponens as a rule step of the inductive family.
example {Γ : Set Proposition} {P Q : Proposition}
    (h1 : Γ ⊢ implication P Q) (h2 : Γ ⊢ P) : Γ ⊢ Q :=
  Ded.mp Γ P Q h1 h2

-- Provable identity (done in the experiment)
-- For every P ∈ Prop, we have ⊢ P → P.
-- ⊢ P → P — Hilbert's identity, from the two implication
-- axiom schemes (`imp₁`, `imp₂`) and MP.
-- Hilbert's identity: the theorem one is taught to prove first, because one must.
theorem imp_self (P : Proposition) : (∅ : Set Proposition) ⊢ implication P P := by
  have h1 : (∅ : Set Proposition) ⊢ implication P (implication (implication P P) P) :=
    Ded.imp_1 (∅ : Set Proposition) P (implication P P)
  have h2 : (∅ : Set Proposition) ⊢ implication P (implication P P) :=
    Ded.imp_1 (∅ : Set Proposition) P P
  have h3 : (∅ : Set Proposition) ⊢
      implication (implication P (implication (implication P P) P))
                  (implication (implication P (implication P P)) (implication P P)) :=
    Ded.imp_2 (∅ : Set Proposition) P (implication P P) P
  have h4 : (∅ : Set Proposition) ⊢
      implication (implication P (implication P P)) (implication P P) :=
    Ded.mp (∅ : Set Proposition) (implication P (implication (implication P P) P))
      (implication (implication P (implication P P)) (implication P P)) h3 h1
  exact Ded.mp (∅ : Set Proposition) (implication P (implication P P)) (implication P P) h4 h2

-- ----------------------------------------------------------------------------
-- Monotonicity and finiteness
-- ----------------------------------------------------------------------------

-- Weakening / monotonicity — if Γ ⊆ Δ and Γ ⊢ P then Δ ⊢ P.
-- A structural induction over every constructor of the `Ded` family: the `assm` case
-- routes the hypothesis through the subset inclusion, and every other constructor is
-- re-emitted at the larger context unchanged.
-- If adding assumptions could break a proof, the logic would be badly designed,
-- and Lean, given the chance to say so, usually does.
theorem weakening {Γ Δ : Set Proposition} (hsub : Γ ⊆ Δ) {P : Proposition} :
    (Γ ⊢ P) → (Δ ⊢ P) := by
  intro h
  induction h with
  | assm Q hmem => exact Ded.assm Δ Q (hsub hmem)
  | imp_1 P' Q' => exact Ded.imp_1 Δ P' Q'
  | imp_2 P' Q' R' => exact Ded.imp_2 Δ P' Q' R'
  | neg_contra P' Q' => exact Ded.neg_contra Δ P' Q'
  | neg_elim P' => exact Ded.neg_elim Δ P'
  | raa P' => exact Ded.raa Δ P'
  | efq P' => exact Ded.efq Δ P'
  | top_intro => exact Ded.top_intro Δ
  | conj_elim_left P' Q' => exact Ded.conj_elim_left Δ P' Q'
  | conj_elim_right P' Q' => exact Ded.conj_elim_right Δ P' Q'
  | conj_intro P' Q' => exact Ded.conj_intro Δ P' Q'
  | disj_intro_left P' Q' => exact Ded.disj_intro_left Δ P' Q'
  | disj_intro_right P' Q' => exact Ded.disj_intro_right Δ P' Q'
  | disj_elim P' Q' R' => exact Ded.disj_elim Δ P' Q' R'
  | mp P' Q' hf hp ihf ihp => exact Ded.mp Δ P' Q' ihf ihp

-- Finite proofs (done in the experiment)
-- Let T ⊆ Prop and P ∈ Prop. Prove that if T ⊢ P, then there exists a finite subset T₀ of T such that T₀ ⊢ P.
-- Compactness of the derivation relation: every proof uses only finitely
-- many hypotheses. Induction on the derivation; the `assm` case needs the single finite
-- set `{P}`, each axiom/rule step needs only `∅`, and MP takes the union
-- of the two IHs' finite subsets, weakening each sub-derivation up to the union.
-- Proofs are finite objects, so this is less a theorem about logic and more a
-- reminder about what proofs are; the reminder is machine-checked.
theorem finite_subproof {T : Set Proposition} {P : Proposition} (h : T ⊢ P) :
    ∃ T₀ : Set Proposition, T₀.Finite ∧ T₀ ⊆ T ∧ T₀ ⊢ P := by
  induction h with
  | assm Q hmem =>
      refine ⟨{Q}, ?_, ?_, ?_⟩
      · exact Set.finite_singleton Q
      · intro x hx; rw [Set.mem_singleton_iff] at hx; rw [hx]; exact hmem
      · exact Ded.assm ({Q} : Set Proposition) Q (by simp)
  | imp_1 P' Q' =>
      refine ⟨∅, ?_, ?_, ?_⟩
      · exact Set.finite_empty
      · simp
      · exact Ded.imp_1 (∅ : Set Proposition) P' Q'
  | imp_2 P' Q' R' =>
      refine ⟨∅, ?_, ?_, ?_⟩
      · exact Set.finite_empty
      · simp
      · exact Ded.imp_2 (∅ : Set Proposition) P' Q' R'
  | neg_contra P' Q' =>
      refine ⟨∅, ?_, ?_, ?_⟩
      · exact Set.finite_empty
      · simp
      · exact Ded.neg_contra (∅ : Set Proposition) P' Q'
  | neg_elim P' =>
      refine ⟨∅, ?_, ?_, ?_⟩
      · exact Set.finite_empty
      · simp
      · exact Ded.neg_elim (∅ : Set Proposition) P'
  | raa P' =>
      refine ⟨∅, ?_, ?_, ?_⟩
      · exact Set.finite_empty
      · simp
      · exact Ded.raa (∅ : Set Proposition) P'
  | efq P' =>
      refine ⟨∅, ?_, ?_, ?_⟩
      · exact Set.finite_empty
      · simp
      · exact Ded.efq (∅ : Set Proposition) P'
  | top_intro =>
      refine ⟨∅, ?_, ?_, ?_⟩
      · exact Set.finite_empty
      · simp
      · exact Ded.top_intro (∅ : Set Proposition)
  | conj_elim_left P' Q' =>
      refine ⟨∅, ?_, ?_, ?_⟩
      · exact Set.finite_empty
      · simp
      · exact Ded.conj_elim_left (∅ : Set Proposition) P' Q'
  | conj_elim_right P' Q' =>
      refine ⟨∅, ?_, ?_, ?_⟩
      · exact Set.finite_empty
      · simp
      · exact Ded.conj_elim_right (∅ : Set Proposition) P' Q'
  | conj_intro P' Q' =>
      refine ⟨∅, ?_, ?_, ?_⟩
      · exact Set.finite_empty
      · simp
      · exact Ded.conj_intro (∅ : Set Proposition) P' Q'
  | disj_intro_left P' Q' =>
      refine ⟨∅, ?_, ?_, ?_⟩
      · exact Set.finite_empty
      · simp
      · exact Ded.disj_intro_left (∅ : Set Proposition) P' Q'
  | disj_intro_right P' Q' =>
      refine ⟨∅, ?_, ?_, ?_⟩
      · exact Set.finite_empty
      · simp
      · exact Ded.disj_intro_right (∅ : Set Proposition) P' Q'
  | disj_elim P' Q' R' =>
      refine ⟨∅, ?_, ?_, ?_⟩
      · exact Set.finite_empty
      · simp
      · exact Ded.disj_elim (∅ : Set Proposition) P' Q' R'
  | mp P' Q' hf hp ihf ihp =>
      rcases ihf with ⟨T1, fin1, hsub1, hd1⟩
      rcases ihp with ⟨T2, fin2, hsub2, hd2⟩
      refine ⟨T1 ∪ T2, ?_, ?_, ?_⟩
      · exact Set.Finite.union fin1 fin2
      · intro x hx
        rcases hx with hx1 | hx2
        · exact hsub1 hx1
        · exact hsub2 hx2
      · exact Ded.mp (T1 ∪ T2) P' Q'
          (weakening (fun x hx => Or.inl hx) hd1)
          (weakening (fun x hx => Or.inr hx) hd2)

-- Deduction Lemma
-- Let T ⊆ Prop and P, Q be propositions. If T ∪ {P} ⊢ Q, then T ⊢ P → Q.
-- Proved by induction on the derivation of Q from T ∪ {P}.
-- The two non-trivial cases:
--   • the assumption Q = P: then T ⊢ P → P is the identity (weakened from ∅);
--   • modus ponens (premises A and A → B): the IHs give T ⊢ P → A and
--     T ⊢ P → (A → B), and the axiom scheme `imp₂` closes T ⊢ P → B.
-- Every other constructor is an axiom scheme provable at any context, smuggled into
-- P → Q by the scheme `imp₁` ("if Q is provable then P → Q is provable").
-- That lift is `imp_intro_of_provable` below.
-- The proof is not clever; it enumerates every constructor and checks. Here we are
-- content to match Lean's preference for thoroughness over wit.

-- If an implication's consequent is provable, so is the whole implication (scheme `imp₁` + MP).
lemma imp_intro_of_provable {T : Set Proposition} {P Q : Proposition}
    (h : T ⊢ Q) : T ⊢ implication P Q :=
      Ded.mp T Q (implication P Q) (Ded.imp_1 T Q P) h

-- ----------------------------------------------------------------------------
-- The Deduction Lemma
-- ----------------------------------------------------------------------------

-- The **Deduction Lemma**: if `Q` is provable from
-- `T ∪ {P}`, then `P → Q` is provable from `T`.  The strategy is described in
-- the comment above `imp_intro_of_provable`; the induction here just threads it
-- through every constructor of the `Ded` family, with Modus Ponens handled by
-- the `imp₂`-glued step below.
-- The machinery is identical to `weakening`'s; what is new is what it says.
-- Either way, Lean checks.
theorem deduction {T : Set Proposition} {P Q : Proposition}
    (h : T ∪ ({P} : Set Proposition) ⊢ Q) : T ⊢ implication P Q := by
  induction h with
  | assm A hmem =>
      rcases hmem with hA | hsing
      · exact imp_intro_of_provable (Ded.assm T A hA)
      · have hAeq : A = P := by simpa using hsing
        rw [hAeq]
        exact weakening (by intro x hx; simp at hx) (imp_self P)
  | imp_1 A B => exact imp_intro_of_provable (Ded.imp_1 T A B)
  | imp_2 A B C => exact imp_intro_of_provable (Ded.imp_2 T A B C)
  | neg_contra A B => exact imp_intro_of_provable (Ded.neg_contra T A B)
  | neg_elim A => exact imp_intro_of_provable (Ded.neg_elim T A)
  | raa A => exact imp_intro_of_provable (Ded.raa T A)
  | efq A => exact imp_intro_of_provable (Ded.efq T A)
  | top_intro => exact imp_intro_of_provable (Ded.top_intro T)
  | conj_elim_left A B => exact imp_intro_of_provable (Ded.conj_elim_left T A B)
  | conj_elim_right A B => exact imp_intro_of_provable (Ded.conj_elim_right T A B)
  | conj_intro A B => exact imp_intro_of_provable (Ded.conj_intro T A B)
  | disj_intro_left A B => exact imp_intro_of_provable (Ded.disj_intro_left T A B)
  | disj_intro_right A B => exact imp_intro_of_provable (Ded.disj_intro_right T A B)
  | disj_elim A B C => exact imp_intro_of_provable (Ded.disj_elim T A B C)
  | mp A B hf hp ihf ihp =>
      exact Ded.mp T (implication P A) (implication P B)
        (Ded.mp T (implication P (implication A B))
                  (implication (implication P A) (implication P B))
                  (Ded.imp_2 T P A B) ihf)
        ihp

-- Hypothetical syllogism: if T ⊢ A → B and T ⊢ B → C then
-- T ⊢ A → C. By the Deduction Lemma: assume A, chained MP gets C.
lemma imp_trans {T : Set Proposition} {A B C : Proposition}
    (hAB : T ⊢ implication A B) (hBC : T ⊢ implication B C) :
    T ⊢ implication A C := by
  apply deduction
  have hA : (T ∪ ({A} : Set Proposition)) ⊢ A := Ded.assm (T ∪ ({A} : Set Proposition)) A (by simp)
  have hAB' : (T ∪ ({A} : Set Proposition)) ⊢ implication A B :=
    weakening (fun x hx => Or.inl hx) hAB
  have hB : (T ∪ ({A} : Set Proposition)) ⊢ B := Ded.mp (T ∪ ({A} : Set Proposition)) A B hAB' hA
  have hBC' : (T ∪ ({A} : Set Proposition)) ⊢ implication B C :=
    weakening (fun x hx => Or.inl hx) hBC
  exact Ded.mp (T ∪ ({A} : Set Proposition)) B C hBC' hB

-- Classical ex falso expressed with the material implication: from provable ¬ A
-- (and A → B being ¬ A ∨ B) we get T ⊢ A → B.
-- Uses `disj_intro_left` on the disjunctive spelling of the implication.
lemma neg_imp {T : Set Proposition} {A B : Proposition} (h : T ⊢ neg A) :
    T ⊢ implication A B :=
  Ded.mp T (neg A) (implication A B) (Ded.disj_intro_left T (neg A) B) h

-- Modus tollens: from T ⊢ A → X and T ⊢ ¬ X, derive T ⊢ ¬ A.
-- disj_elim resolves the disjunctive A → X = ¬ A ∨ X against
-- ¬ A (reflexive) and X → ¬ A (which `neg_imp` supplies from provable ¬ X).
lemma modus_tollens {T : Set Proposition} {A X : Proposition}
    (hAX : T ⊢ implication A X) (hnegX : T ⊢ neg X) : T ⊢ neg A := by
  have hAXd : T ⊢ disj (neg A) X := by simpa [implication] using hAX
  have hAA : T ⊢ implication (neg A) (neg A) :=
    weakening (by intro x hx; simp at hx) (imp_self (neg A))
  have hXA : T ⊢ implication X (neg A) := neg_imp hnegX
  have hstep : T ⊢ implication (disj (neg A) X) (neg A) :=
    Ded.mp T (implication X (neg A)) (implication (disj (neg A) X) (neg A))
      (Ded.mp T (implication (neg A) (neg A))
                (implication (implication X (neg A)) (implication (disj (neg A) X) (neg A)))
                (Ded.disj_elim T (neg A) X (neg A))
                hAA)
      hXA
  exact Ded.mp T (disj (neg A) X) (neg A) hstep hAXd

-- Consequences of the derivation rules
-- Prove the following statements:
-- (1) ⊢ (P → Q) → (¬ Q → ¬ P);
-- (2) ⊢ ¬ (P ∨ Q) → (¬ P ∧ ¬ Q);
-- (3) {P ∨ Q, ¬ R → ¬ Q, ¬ P} ⊢ R.
-- (1) — contraposition, by the Deduction Lemma twice and modus tollens.
-- Supervised homework; each item was expected to be true before Lean confirmed it,
-- which is the customary order of discovery in these matters.
theorem contraposition_provable {P Q : Proposition} :
    (∅ : Set Proposition) ⊢ implication (implication P Q) (implication (neg Q) (neg P)) := by
  apply deduction
  apply deduction
  have hPQ : ((∅ : Set Proposition) ∪ {implication P Q}) ∪ {neg Q} ⊢ implication P Q :=
    Ded.assm (((∅ : Set Proposition) ∪ {implication P Q}) ∪ {neg Q})
             (implication P Q) (by simp)
  have hnQ : ((∅ : Set Proposition) ∪ {implication P Q}) ∪ {neg Q} ⊢ neg Q :=
    Ded.assm (((∅ : Set Proposition) ∪ {implication P Q}) ∪ {neg Q}) (neg Q) (by simp)
  exact modus_tollens hPQ hnQ

-- (2) — one of De Morgan's laws, by the Deduction Lemma then modus tollens twice.
theorem de_morgan_not_disj {P Q : Proposition} :
    (∅ : Set Proposition) ⊢ implication (neg (disj P Q)) (conj (neg P) (neg Q)) := by
  apply deduction
  have hPPQ : (∅ : Set Proposition) ∪ {neg (disj P Q)} ⊢ implication P (disj P Q) :=
    Ded.disj_intro_left ((∅ : Set Proposition) ∪ {neg (disj P Q)}) P Q
  have hQPQ : (∅ : Set Proposition) ∪ {neg (disj P Q)} ⊢ implication Q (disj P Q) :=
    Ded.disj_intro_right ((∅ : Set Proposition) ∪ {neg (disj P Q)}) P Q
  have hn : (∅ : Set Proposition) ∪ {neg (disj P Q)} ⊢ neg (disj P Q) :=
    Ded.assm ((∅ : Set Proposition) ∪ {neg (disj P Q)}) (neg (disj P Q)) (by simp)
  have hnP : (∅ : Set Proposition) ∪ {neg (disj P Q)} ⊢ neg P := modus_tollens hPPQ hn
  have hnQ : (∅ : Set Proposition) ∪ {neg (disj P Q)} ⊢ neg Q := modus_tollens hQPQ hn
  exact Ded.mp ((∅ : Set Proposition) ∪ {neg (disj P Q)}) (neg Q) (conj (neg P) (neg Q))
    (Ded.mp ((∅ : Set Proposition) ∪ {neg (disj P Q)}) (neg P)
            (implication (neg Q) (conj (neg P) (neg Q)))
            (Ded.conj_intro ((∅ : Set Proposition) ∪ {neg (disj P Q)}) (neg P) (neg Q)) hnP)
    hnQ

-- (3) — a theory argument, by the disjunction rule with `neg_contra` contraposing
-- ¬ R → ¬ Q into Q → R.
theorem disj_neg_derive_provable {P Q R : Proposition} :
    ({disj P Q, implication (neg R) (neg Q), neg P} : Set Proposition) ⊢ R := by
  let T : Set Proposition := {disj P Q, implication (neg R) (neg Q), neg P}
  have hPQ : T ⊢ disj P Q := Ded.assm T (disj P Q) (by simp [T])
  have hRneqQ : T ⊢ implication (neg R) (neg Q) :=
    Ded.assm T (implication (neg R) (neg Q)) (by simp [T])
  have hnP : T ⊢ neg P := Ded.assm T (neg P) (by simp [T])
  have hQR : T ⊢ implication Q R :=
    Ded.mp T (implication (neg R) (neg Q)) (implication Q R) (Ded.neg_contra T R Q) hRneqQ
  have hPR : T ⊢ implication P R := neg_imp hnP
  exact Ded.mp T (disj P Q) R
    (Ded.mp T (implication Q R) (implication (disj P Q) R)
      (Ded.mp T (implication P R) (implication (implication Q R) (implication (disj P Q) R))
                (Ded.disj_elim T P Q R)
                hPR)
      hQR)
    hPQ

-- Definition — Logically equivalent in T
-- Let T ⊆ Prop and P, Q be propositions. We say that P and Q are **logically equivalent in T** (denoted by P ∼_T Q) if T ⊢ P ↔ Q.
-- The biconditional ↔ is `Semantics.bicond`; P ∼_T Q means
-- T ⊢ (P → Q) ∧ (Q → P).
def LogicallyEquivalentIn (T : Set Proposition) (P Q : Proposition) : Prop :=
  T ⊢ bicond P Q

-- Equivalence relation on propositions
-- For every T ⊆ Prop, the relation ∼_T is an equivalence relation on Prop.
-- Reflexivity: P ↔ P is provable by the identity, and `bicond` glues its two halves.
-- An equivalence relation, as the exercise demands; nothing here surprises anyone,
-- least of all Lean.
theorem logicallyEquivalent_refl (T : Set Proposition) (P : Proposition) :
    LogicallyEquivalentIn T P P := by
  unfold LogicallyEquivalentIn
  have hPP : T ⊢ implication P P :=
    weakening (by intro x hx; simp at hx) (imp_self P)
  exact Ded.mp T (implication P P) (bicond P P)
    (Ded.mp T (implication P P) (implication (implication P P) (bicond P P))
              (Ded.conj_intro T (implication P P) (implication P P)) hPP)
    hPP

-- Symmetry: swap the two halves of bicond P Q with `conj_elim_*` and `conj_intro`.
theorem logicallyEquivalent_symm {T : Set Proposition} {P Q : Proposition}
    (h : LogicallyEquivalentIn T P Q) : LogicallyEquivalentIn T Q P := by
  unfold LogicallyEquivalentIn at *
  have hPQ : T ⊢ implication P Q :=
    Ded.mp T (bicond P Q) (implication P Q)
      (Ded.conj_elim_left T (implication P Q) (implication Q P)) h
  have hQP : T ⊢ implication Q P :=
    Ded.mp T (bicond P Q) (implication Q P)
      (Ded.conj_elim_right T (implication P Q) (implication Q P)) h
  exact Ded.mp T (implication P Q) (bicond Q P)
    (Ded.mp T (implication Q P) (implication (implication P Q) (bicond Q P))
              (Ded.conj_intro T (implication Q P) (implication P Q)) hQP)
    hPQ

-- Transitivity: hypothetic syllogism on each implication direction, then re-glue `bicond`.
theorem logicallyEquivalent_trans {T : Set Proposition} {P Q R : Proposition}
    (hPQ : LogicallyEquivalentIn T P Q) (hQR : LogicallyEquivalentIn T Q R) :
    LogicallyEquivalentIn T P R := by
  unfold LogicallyEquivalentIn at *
  have pQ : T ⊢ implication P Q :=
    Ded.mp T (bicond P Q) (implication P Q)
      (Ded.conj_elim_left T (implication P Q) (implication Q P)) hPQ
  have qP : T ⊢ implication Q P :=
    Ded.mp T (bicond P Q) (implication Q P)
      (Ded.conj_elim_right T (implication P Q) (implication Q P)) hPQ
  have qR : T ⊢ implication Q R :=
    Ded.mp T (bicond Q R) (implication Q R)
      (Ded.conj_elim_left T (implication Q R) (implication R Q)) hQR
  have rQ : T ⊢ implication R Q :=
    Ded.mp T (bicond Q R) (implication R Q)
      (Ded.conj_elim_right T (implication Q R) (implication R Q)) hQR
  have pR : T ⊢ implication P R := imp_trans pQ qR
  have rP : T ⊢ implication R P := imp_trans rQ qP
  exact Ded.mp T (implication R P) (bicond P R)
    (Ded.mp T (implication P R) (implication (implication R P) (bicond P R))
              (Ded.conj_intro T (implication P R) (implication R P)) pR)
    rP

-- Hence ∼_T is an equivalence relation on propositions.
theorem logicallyEquivalent_equiv (T : Set Proposition) :
    Equivalence (LogicallyEquivalentIn T) := by
  refine ⟨logicallyEquivalent_refl T, ?_, ?_⟩
  · intro a b h; exact logicallyEquivalent_symm h
  · intro a b c h₁ h₂; exact logicallyEquivalent_trans h₁ h₂

end PropositionalLogic
-- The definition of the deduction / provability relation T ⊢ P (the Ded inductive family) is modeled on https://github.com/guodk/PropLogicLean
-- and the inductive-family encoding style also follows https://github.com/m4lvin/lean4-pdl