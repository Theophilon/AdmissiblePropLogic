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

open Admissibility

-- ----------------------------------------------------------------------------
-- Axiom schemes are tautologies (soundness of the single-axiom presentation)
-- ----------------------------------------------------------------------------
-- Each is `Tautology`, i.e. true under every truth assignment: expand the
-- abbreviation layers with the `eval_*` lemmas, then the goal is a closed
-- truth-functional `Bool` identity closed by `decide`.
theorem tautology_top_axiom : Tautology top := by
  intro t
  simp [eval_top]
theorem tautology_disj_intro_left {P Q : Proposition} :
    Tautology (implication P (disj P Q)) := by
  intro t
  simp only [eval_implication, eval_disj]
  cases eval t P <;> cases eval t Q <;> decide
theorem tautology_disj_intro_right {P Q : Proposition} :
    Tautology (implication P (disj Q P)) := by
  intro t
  simp only [eval_implication, eval_disj]
  cases eval t P <;> cases eval t Q <;> decide
theorem tautology_imp_1 {P Q : Proposition} :
    Tautology (implication P (implication Q P)) := by
  intro t
  simp only [eval_implication]
  cases eval t P <;> cases eval t Q <;> decide
theorem tautology_imp_2 {P Q R : Proposition} :
    Tautology (implication (implication P (implication Q R))
                            (implication (implication P Q) (implication P R))) := by
  intro t
  simp only [eval_implication]
  cases eval t P <;> cases eval t Q <;> cases eval t R <;> decide
theorem tautology_neg_contra {P Q : Proposition} :
    Tautology (implication (implication (neg P) (neg Q)) (implication Q P)) := by
  intro t
  simp only [eval_implication, eval_neg]
  cases eval t P <;> cases eval t Q <;> decide
theorem tautology_neg_elim {P : Proposition} :
    Tautology (implication P (implication (neg P) bot)) := by
  intro t
  simp only [eval_implication, eval_neg, eval_bot]
  cases eval t P <;> decide
theorem tautology_raa {P : Proposition} :
    Tautology (implication (implication (neg P) bot) P) := by
  intro t
  simp only [eval_implication, eval_neg, eval_bot]
  cases eval t P <;> decide
theorem tautology_conj_elim_left {P Q : Proposition} :
    Tautology (implication (conj P Q) P) := by
  intro t
  simp only [eval_implication, eval_conj]
  cases eval t P <;> cases eval t Q <;> decide
theorem tautology_conj_elim_right {P Q : Proposition} :
    Tautology (implication (conj P Q) Q) := by
  intro t
  simp only [eval_implication, eval_conj]
  cases eval t P <;> cases eval t Q <;> decide
theorem tautology_conj_intro {P Q : Proposition} :
    Tautology (implication P (implication Q (conj P Q))) := by
  intro t
  simp only [eval_implication, eval_conj]
  cases eval t P <;> cases eval t Q <;> decide
theorem tautology_disj_elim {P Q R : Proposition} :
    Tautology (implication (implication P R)
              (implication (implication Q R) (implication (disj P Q) R))) := by
  intro t
  simp only [eval_implication, eval_disj]
  cases eval t P <;> cases eval t Q <;> cases eval t R <;> decide

-- ----------------------------------------------------------------------------
-- The provability relation Ded
-- ----------------------------------------------------------------------------

-- Inductive family of derivations: each axiom scheme is a constructor and
-- Modus Ponens is the single rule.  The `Ded` family keeps exactly the six
-- primitive schemes of the classical Hilbert base — assumption, the two
-- implication schemes, contraposition-into-`neg` (`neg_contra`), and RAA —
-- together with the Modus Ponens rule.  Every other former scheme (`top`,
-- `efq`, `neg_elim`, `contrapos`, `conj_intro`, `disj_intro_*`, `disj_elim`,
-- `conj_elim_*`) is re-derived below as a theorem over this six-constructor
-- base: {imp_1, imp_2, neg_contra, raa} is (with `mp`) classically complete,
-- so the three former axiom schemes `neg_elim`, `contrapos` and `conj_intro`
-- are theorems (`deriv_neg_elim`, `deriv_contrapos`, `deriv_conj_intro`).
inductive Ded : Set Proposition → Proposition → Prop
  | assm         : ∀ Γ P, P ∈ Γ → Ded Γ P
  | imp_1        : ∀ Γ P Q, Ded Γ (implication P (implication Q P))
  | imp_2        : ∀ Γ P Q R,
      Ded Γ (implication (implication P (implication Q R))
                          (implication (implication P Q) (implication P R)))
  | neg_contra   : ∀ Γ P Q, Ded Γ (implication (implication (neg P) (neg Q)) (implication Q P))
  | raa          : ∀ Γ P, Ded Γ (implication (implication (neg P) bot) P)
  | mp : ∀ Γ P Q, Ded Γ (implication P Q) → Ded Γ P → Ded Γ Q

notation : 45 Γ "⊢" φ => Ded Γ φ

theorem provable_of_mem {Γ : Set Proposition} {P : Proposition} (h : P ∈ Γ) : Γ ⊢ P :=
  Ded.assm Γ P h

example {Γ : Set Proposition} {P Q : Proposition}
    (h1 : Γ ⊢ implication P Q) (h2 : Γ ⊢ P) : Γ ⊢ Q :=
  Ded.mp Γ P Q h1 h2

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

theorem weakening {Γ Δ : Set Proposition} (hsub : Γ ⊆ Δ) {P : Proposition} :
    (Γ ⊢ P) → (Δ ⊢ P) := by
  intro h
  induction h with
  | assm Q hmem => exact Ded.assm Δ Q (hsub hmem)
  | imp_1 P1 Q1 => exact Ded.imp_1 Δ P1 Q1
  | imp_2 P1 Q1 R1 => exact Ded.imp_2 Δ P1 Q1 R1
  | neg_contra P1 Q1 => exact Ded.neg_contra Δ P1 Q1
  | raa P1 => exact Ded.raa Δ P1
  | mp P1 Q1 hf hp ihf ihp => exact Ded.mp Δ P1 Q1 ihf ihp

-- Compactness of the derivation relation: a derivation is finite.
theorem finite_subproof {T : Set Proposition} {P : Proposition} (h : T ⊢ P) :
    ∃ T₀ : Set Proposition, T₀.Finite ∧ T₀ ⊆ T ∧ T₀ ⊢ P := by
  induction h with
  | assm Q hmem =>
      refine ⟨{Q}, ?_, ?_, ?_⟩
      · exact Set.finite_singleton Q
      · intro x hx; rw [Set.mem_singleton_iff] at hx; rw [hx]; exact hmem
      · exact Ded.assm ({Q} : Set Proposition) Q (by simp)
  | imp_1 P1 Q1 =>
      exact ⟨∅, Set.finite_empty, by simp, Ded.imp_1 (∅ : Set Proposition) P1 Q1⟩
  | imp_2 P1 Q1 R1 =>
      exact ⟨∅, Set.finite_empty, by simp, Ded.imp_2 (∅ : Set Proposition) P1 Q1 R1⟩
  | neg_contra P1 Q1 =>
      exact ⟨∅, Set.finite_empty, by simp, Ded.neg_contra (∅ : Set Proposition) P1 Q1⟩
  | raa P1 =>
      exact ⟨∅, Set.finite_empty, by simp, Ded.raa (∅ : Set Proposition) P1⟩
  | mp P1 Q1 hf hp ihf ihp =>
      rcases ihf with ⟨T1, fin1, hsub1, hd1⟩
      rcases ihp with ⟨T2, fin2, hsub2, hd2⟩
      refine ⟨T1 ∪ T2, ?_, ?_, ?_⟩
      · exact Set.Finite.union fin1 fin2
      · intro x hx
        rcases hx with hx1 | hx2
        · exact hsub1 hx1
        · exact hsub2 hx2
      · exact Ded.mp (T1 ∪ T2) P1 Q1
          (weakening (fun x hx => Or.inl hx) hd1)
          (weakening (fun x hx => Or.inr hx) hd2)

lemma imp_intro_of_provable {T : Set Proposition} {P Q : Proposition}
    (h : T ⊢ Q) : T ⊢ implication P Q :=
  Ded.mp T Q (implication P Q) (Ded.imp_1 T Q P) h

-- The Deduction Lemma: if `T ∪ {P} ⊢ Q`, then `T ⊢ P → Q`.
lemma deduction {T : Set Proposition} {P Q : Proposition}
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
  | raa A => exact imp_intro_of_provable (Ded.raa T A)
  | mp A B hf hp ihf ihp =>
      exact Ded.mp T (implication P A) (implication P B)
        (Ded.mp T (implication P (implication A B))
                  (implication (implication P A) (implication P B))
                  (Ded.imp_2 T P A B) ihf)
        ihp

-- Hypothetical syllogism: from `A → B` and `B → C` get `A → C`.
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

-- ----------------------------------------------------------------------------
-- Helpers and derived schemes
-- ----------------------------------------------------------------------------

-- From contradictory hypotheses `P` and `¬P` we get `bot`.  This is proven
-- directly over the primitive schemes: instantiate `neg_contra` at `bot`/`P`
-- to get `(¬bot → ¬P) → (P → bot)`, discharge the antecedent by
-- `imp_intro_of_provable` from the given `¬P`, then two Modus Ponens.
lemma bot_of_contra {T : Set Proposition} {P : Proposition} (hP : T ⊢ P) (hN : T ⊢ neg P) :
    T ⊢ bot := by
  have hA : T ⊢ implication (neg bot) (neg P) := imp_intro_of_provable hN
  have hB : T ⊢ implication (implication (neg bot) (neg P)) (implication P bot) :=
    Ded.neg_contra T bot P
  have hPB : T ⊢ implication P bot :=
    Ded.mp T (implication (neg bot) (neg P)) (implication P bot) hB hA
  exact Ded.mp T P bot hPB hP

-- Double-negation elimination `¬¬P → P` (classical; via RAA).  Under `¬¬P`,
-- `bot_of_contra` on the assumed `¬P` yields `bot`, so `¬P → bot` holds and
-- RAA hands back `P`.
theorem deriv_double_neg_elim {Γ : Set Proposition} {P : Proposition} :
    Γ ⊢ implication (neg (neg P)) P := by
  apply deduction
  let S : Set Proposition := Γ ∪ ({neg (neg P)} : Set Proposition)
  change S ⊢ P
  have hB : S ⊢ implication (neg P) bot := by
    apply deduction
    let S2 : Set Proposition := S ∪ ({neg P} : Set Proposition)
    change S2 ⊢ bot
    have hNP : S2 ⊢ neg P := Ded.assm S2 (neg P) (by simp [S2, S])
    have hNNP : S2 ⊢ neg (neg P) := weakening (fun x hx => Or.inl hx)
      (Ded.assm S (neg (neg P)) (by simp [S]))
    exact bot_of_contra (P := neg P) hNP hNNP
  exact Ded.mp S (implication (neg P) bot) P (Ded.raa S P) hB

-- Negation introduction `(P → bot) → ¬P`.  Classical, via RAA for `¬P`: it
-- suffices to show `¬¬P → bot`, and under `¬¬P` double-negation elimination
-- produces `P`, which `P → bot` turns into `bot`.
theorem deriv_neg_intro {Γ : Set Proposition} {P : Proposition} :
    Γ ⊢ implication (implication P bot) (neg P) := by
  apply deduction
  let S : Set Proposition := Γ ∪ ({implication P bot} : Set Proposition)
  change S ⊢ neg P
  have hB : S ⊢ implication (neg (neg P)) bot := by
    apply deduction
    let S2 : Set Proposition := S ∪ ({neg (neg P)} : Set Proposition)
    change S2 ⊢ bot
    have hPB : S2 ⊢ implication P bot := Ded.assm S2 (implication P bot) (by simp [S2, S])
    have hNNP : S2 ⊢ neg (neg P) := Ded.assm S2 (neg (neg P)) (by simp [S2, S])
    have hP : S2 ⊢ P := Ded.mp S2 (neg (neg P)) P (deriv_double_neg_elim (P := P)) hNNP
    exact Ded.mp S2 P bot hPB hP
  exact Ded.mp S (implication (neg (neg P)) bot) (neg P) (Ded.raa S (neg P)) hB

-- `P → (¬P → bot)`: from `P` and `¬P` the contradiction lemma yields `bot`.
theorem deriv_neg_elim {Γ : Set Proposition} {P : Proposition} :
    Γ ⊢ implication P (implication (neg P) bot) := by
  apply deduction
  apply deduction
  let S : Set Proposition := (Γ ∪ ({P} : Set Proposition)) ∪ ({neg P} : Set Proposition)
  change S ⊢ bot
  have hP : S ⊢ P := Ded.assm S P (by simp [S])
  have hN : S ⊢ neg P := Ded.assm S (neg P) (by simp [S])
  exact bot_of_contra hP hN

-- Contraposition `(P → Q) → (¬Q → ¬P)`: under `P → Q` and `¬Q`, an assumed
-- `P` yields `Q` and then `bot`, so `P → bot`, and negation-introduction
-- closes the goal with `¬P`.
theorem deriv_contrapos {Γ : Set Proposition} {P Q : Proposition} :
    Γ ⊢ implication (implication P Q) (implication (neg Q) (neg P)) := by
  apply deduction
  apply deduction
  let S : Set Proposition := (Γ ∪ ({implication P Q} : Set Proposition)) ∪ ({neg Q} : Set Proposition)
  change S ⊢ neg P
  have hPB : S ⊢ implication P bot := by
    apply deduction
    let S2 : Set Proposition := S ∪ ({P} : Set Proposition)
    change S2 ⊢ bot
    have hPQ : S2 ⊢ implication P Q := Ded.assm S2 (implication P Q) (by simp [S2, S])
    have hP : S2 ⊢ P := Ded.assm S2 P (by simp [S2, S])
    have hQ : S2 ⊢ Q := Ded.mp S2 P Q hPQ hP
    have hNQ : S2 ⊢ neg Q := Ded.assm S2 (neg Q) (by simp [S2, S])
    exact bot_of_contra hQ hNQ
  exact Ded.mp S (implication P bot) (neg P) (deriv_neg_intro (P := P)) hPB

-- Conjunction introduction `P → Q → (P ∧ Q)`, where `conj P Q = ¬(P → ¬Q)`.
theorem deriv_conj_intro {Γ : Set Proposition} {P Q : Proposition} :
    Γ ⊢ implication P (implication Q (conj P Q)) := by
  apply deduction
  apply deduction
  let S : Set Proposition := (Γ ∪ ({P} : Set Proposition)) ∪ ({Q} : Set Proposition)
  let M : Proposition := implication P (neg Q)
  change S ⊢ conj P Q
  change S ⊢ neg M
  have hR : S ⊢ implication (implication M bot) (neg M) := deriv_neg_intro (P := M)
  have hB : S ⊢ implication M bot := by
    apply deduction
    let S2 : Set Proposition := S ∪ ({M} : Set Proposition)
    change S2 ⊢ bot
    have hP : S2 ⊢ P := Ded.assm S2 P (by simp [S2, S])
    have hM : S2 ⊢ M := Ded.assm S2 M (by simp [S2, S])
    have hNQ : S2 ⊢ neg Q := Ded.mp S2 P (neg Q) hM hP
    have hQ : S2 ⊢ Q := Ded.assm S2 Q (by simp [S2, S])
    exact bot_of_contra hQ hNQ
  exact Ded.mp S (implication M bot) (neg M) hR hB

-- Modus tollens: from `A → X` and `¬ X` get `¬ A`, via the derived
-- contraposition theorem `(A → X) → (¬ X → ¬ A)`.
theorem modus_tollens {T : Set Proposition} {A X : Proposition}
    (hAX : T ⊢ implication A X) (hnegX : T ⊢ neg X) : T ⊢ neg A := by
  have hC : T ⊢ implication (implication A X) (implication (neg X) (neg A)) :=
    deriv_contrapos (P := A) (Q := X)
  have hN1 : T ⊢ implication (neg X) (neg A) :=
    Ded.mp T (implication A X) (implication (neg X) (neg A)) hC hAX
  exact Ded.mp T (neg X) (neg A) hN1 hnegX

-- True: `⊤` is provable, because it *is* the identity `P₀ → P₀`.
theorem deriv_top_intro (Γ : Set Proposition) : Γ ⊢ top := by
  change Γ ⊢ implication (var 0) (var 0)
  exact weakening (by intro x hx; simp at hx) (imp_self (var 0))

-- Ex falso: `⊥ → P` follows from RAA.
theorem deriv_efq {Γ : Set Proposition} {P : Proposition} : Γ ⊢ implication bot P := by
  apply deduction
  let S : Set Proposition := Γ ∪ ({bot} : Set Proposition)
  change S ⊢ P
  have hb : S ⊢ bot := Ded.assm S bot (by simp [S])
  have hN : S ⊢ implication (neg P) bot := imp_intro_of_provable hb
  exact Ded.mp S (implication (neg P) bot) P (Ded.raa S P) hN

-- From provable `¬ A`, we can assert `A → B` for arbitrary `B`.
lemma neg_imp {T : Set Proposition} {A B : Proposition} (h : T ⊢ neg A) :
    T ⊢ implication A B := by
  apply deduction
  let S : Set Proposition := T ∪ ({A} : Set Proposition)
  change S ⊢ B
  have hA : S ⊢ A := Ded.assm S A (by simp [S])
  have hN : S ⊢ neg A := weakening (fun x hx => Or.inl hx) h
  have hbot : S ⊢ bot := bot_of_contra hA hN
  exact Ded.mp S bot B (deriv_efq (P := B)) hbot

-- `Q → (P ∨ Q)` is the axiom scheme `imp₁` applied to the disjunction `¬P → Q`.
theorem deriv_disj_intro_right {Γ : Set Proposition} {P Q : Proposition} :
    Γ ⊢ implication Q (disj P Q) := Ded.imp_1 Γ Q (neg P)

-- `P → (¬ P → Q)` from the contradictory premises.
theorem deriv_disj_intro_left {Γ : Set Proposition} {P Q : Proposition} :
    Γ ⊢ implication P (disj P Q) := by
  apply deduction
  apply deduction
  let S : Set Proposition := (Γ ∪ ({P} : Set Proposition)) ∪ ({neg P} : Set Proposition)
  change S ⊢ Q
  have hP : S ⊢ P := Ded.assm S P (by simp [S])
  have hnP : S ⊢ neg P := Ded.assm S (neg P) (by simp [S])
  have hbot : S ⊢ bot := bot_of_contra hP hnP
  exact Ded.mp S bot Q (deriv_efq (P := Q)) hbot

-- Disjunction elimination by proof-by-cases in the `¬P → Q` encoding.
theorem deriv_disj_elim {Γ : Set Proposition} {P Q R : Proposition}
    : Γ ⊢ implication (implication P R)
        (implication (implication Q R) (implication (disj P Q) R)) := by
  apply deduction
  apply deduction
  apply deduction
  let S : Set Proposition :=
    (Γ ∪ ({implication P R} : Set Proposition)) ∪ {implication Q R} ∪ {disj P Q}
  change S ⊢ R
  have hNB : S ⊢ implication (neg R) bot := by
    apply deduction
    let S2 : Set Proposition := S ∪ ({neg R} : Set Proposition)
    change S2 ⊢ bot
    have hNR : S2 ⊢ neg R := Ded.assm S2 (neg R) (by simp [S2, S])
    have hPR : S2 ⊢ implication P R := Ded.assm S2 (implication P R) (by simp [S2, S])
    have hQR : S2 ⊢ implication Q R := Ded.assm S2 (implication Q R) (by simp [S2, S])
    have hPDQ : S2 ⊢ implication (neg P) Q := Ded.assm S2 (implication (neg P) Q) (by simp [S2, S, disj, implication])
    have hNP : S2 ⊢ neg P := modus_tollens hPR hNR
    have hQ : S2 ⊢ Q := Ded.mp S2 (neg P) Q hPDQ hNP
    have hR : S2 ⊢ R := Ded.mp S2 Q R hQR hQ
    exact bot_of_contra hR hNR
  exact Ded.mp S (implication (neg R) bot) R (Ded.raa S R) hNB

-- `(P ∧ Q) → P`, unpacking `∧` as `¬(P → ¬Q)`: RAA for `P` against `¬(P → ¬Q)`.
theorem deriv_conj_elim_left {Γ : Set Proposition} {P Q : Proposition} :
    Γ ⊢ implication (conj P Q) P := by
  apply deduction
  let S : Set Proposition := Γ ∪ ({conj P Q} : Set Proposition)
  change S ⊢ P
  have hNPB : S ⊢ implication (neg P) bot := by
    apply deduction
    let S2 : Set Proposition := S ∪ ({neg P} : Set Proposition)
    change S2 ⊢ bot
    have hConj : S2 ⊢ conj P Q := Ded.assm S2 (conj P Q) (by simp [S2, S])
    have hNegP : S2 ⊢ neg P := Ded.assm S2 (neg P) (by simp [S2, S])
    have hPQ : S2 ⊢ implication P (neg Q) := neg_imp hNegP
    have hConj' : S2 ⊢ neg (implication P (neg Q)) := by simpa [conj, implication] using hConj
    exact bot_of_contra hPQ hConj'
  exact Ded.mp S (implication (neg P) bot) P (Ded.raa S P) hNPB

-- `(P ∧ Q) → Q`, the mirror using `imp_intro_of_provable` to get `P → ¬ Q`
-- from the assumed `¬ Q`.
theorem deriv_conj_elim_right {Γ : Set Proposition} {P Q : Proposition} :
    Γ ⊢ implication (conj P Q) Q := by
  apply deduction
  let S : Set Proposition := Γ ∪ ({conj P Q} : Set Proposition)
  change S ⊢ Q
  have hNQB : S ⊢ implication (neg Q) bot := by
    apply deduction
    let S2 : Set Proposition := S ∪ ({neg Q} : Set Proposition)
    change S2 ⊢ bot
    have hConj : S2 ⊢ conj P Q := Ded.assm S2 (conj P Q) (by simp [S2, S])
    have hNegQ : S2 ⊢ neg Q := Ded.assm S2 (neg Q) (by simp [S2, S])
    have hPQ : S2 ⊢ implication P (neg Q) := imp_intro_of_provable hNegQ
    have hConj' : S2 ⊢ neg (implication P (neg Q)) := by simpa [conj, implication] using hConj
    exact bot_of_contra hPQ hConj'
  exact Ded.mp S (implication (neg Q) bot) Q (Ded.raa S Q) hNQB

-- (1) — contraposition, by the Deduction Lemma twice and modus tollens.
theorem contraposition_provable {P Q : Proposition} :
    (∅ : Set Proposition) ⊢ implication (implication P Q) (implication (neg Q) (neg P)) := by
  apply deduction
  apply deduction
  have hPQ : ((∅ : Set Proposition) ∪ {implication P Q}) ∪ {neg Q} ⊢ implication P Q :=
    Ded.assm (((∅ : Set Proposition) ∪ {implication P Q}) ∪ {neg Q}) (implication P Q) (by simp)
  have hnQ : (((∅ : Set Proposition) ∪ {implication P Q}) ∪ {neg Q}) ⊢ neg Q :=
    Ded.assm (((∅ : Set Proposition) ∪ {implication P Q}) ∪ {neg Q}) (neg Q) (by simp)
  exact modus_tollens hPQ hnQ

-- (2) one of De Morgan's laws.
theorem de_morgan_not_disj {P Q : Proposition} :
    (∅ : Set Proposition) ⊢ implication (neg (disj P Q)) (conj (neg P) (neg Q)) := by
  apply deduction
  let T : Set Proposition := (∅ : Set Proposition) ∪ {neg (disj P Q)}
  change T ⊢ conj (neg P) (neg Q)
  have hPPQ : T ⊢ implication P (disj P Q) := deriv_disj_intro_left (Γ := T) (P := P) (Q := Q)
  have hQPQ : T ⊢ implication Q (disj P Q) := deriv_disj_intro_right (Γ := T) (P := P) (Q := Q)
  have hneg : T ⊢ neg (disj P Q) := Ded.assm T (neg (disj P Q)) (by simp [T])
  have hnP : T ⊢ neg P := modus_tollens hPPQ hneg
  have hnQ : T ⊢ neg Q := modus_tollens hQPQ hneg
  have hCI : T ⊢ implication (neg P) (implication (neg Q) (conj (neg P) (neg Q))) :=
    deriv_conj_intro (P := neg P) (Q := neg Q)
  have h1 : T ⊢ implication (neg Q) (conj (neg P) (neg Q)) :=
    Ded.mp T (neg P) (implication (neg Q) (conj (neg P) (neg Q))) hCI hnP
  exact Ded.mp T (neg Q) (conj (neg P) (neg Q)) h1 hnQ

-- (3) a theory argument with negation `neg_contra` contraposing `¬R → ¬Q` into `Q → R`.
theorem disj_neg_derive_provable {P Q R : Proposition} :
    ({disj P Q, implication (neg R) (neg Q), neg P} : Set Proposition) ⊢ R := by
  let T : Set Proposition := {disj P Q, implication (neg R) (neg Q), neg P}
  have hPQ : T ⊢ disj P Q := Ded.assm T (disj P Q) (by simp [T])
  have hNegRQ : T ⊢ implication (neg R) (neg Q) :=
    Ded.assm T (implication (neg R) (neg Q)) (by simp [T])
  have hnP : T ⊢ neg P := Ded.assm T (neg P) (by simp [T])
  have hQR : T ⊢ implication Q R :=
    Ded.mp T (implication (neg R) (neg Q)) (implication Q R) (Ded.neg_contra T R Q) hNegRQ
  have hPR : T ⊢ implication P R := neg_imp hnP
  have hdel : T ⊢ implication (implication P R)
        (implication (implication Q R) (implication (disj P Q) R)) :=
    deriv_disj_elim (Γ := T) (P := P) (Q := Q) (R := R)
  have h1 : T ⊢ implication (implication Q R) (implication (disj P Q) R) :=
    Ded.mp T (implication P R) (implication (implication Q R) (implication (disj P Q) R)) hdel hPR
  have h2 : T ⊢ implication (disj P Q) R :=
    Ded.mp T (implication Q R) (implication (disj P Q) R) h1 hQR
  exact Ded.mp T (disj P Q) R h2 hPQ

-- Definition — Logically equivalent in T
def LogicallyEquivalentIn (T : Set Proposition) (P Q : Proposition) : Prop :=
  T ⊢ bicond P Q

theorem logicallyEquivalent_refl (T : Set Proposition) (P : Proposition) :
    LogicallyEquivalentIn T P P := by
  unfold LogicallyEquivalentIn
  have hPP : T ⊢ implication P P := weakening (by intro x hx; simp at hx) (imp_self P)
  exact Ded.mp T (implication P P) (bicond P P)
    (Ded.mp T (implication P P) (implication (implication P P) (bicond P P))
              (deriv_conj_intro (P := implication P P) (Q := implication P P)) hPP)
    hPP

theorem logicallyEquivalent_symm {T : Set Proposition} {P Q : Proposition}
    (h : LogicallyEquivalentIn T P Q) : LogicallyEquivalentIn T Q P := by
  unfold LogicallyEquivalentIn at *
  have hPQ : T ⊢ implication P Q :=
    Ded.mp T (bicond P Q) (implication P Q)
      (deriv_conj_elim_left (Γ := T) (P := implication P Q) (Q := implication Q P)) h
  have hQP : T ⊢ implication Q P :=
    Ded.mp T (bicond P Q) (implication Q P)
      (deriv_conj_elim_right (Γ := T) (P := implication P Q) (Q := implication Q P)) h
  exact Ded.mp T (implication P Q) (bicond Q P)
    (Ded.mp T (implication Q P) (implication (implication P Q) (bicond Q P))
              (deriv_conj_intro (P := implication Q P) (Q := implication P Q)) hQP)
    hPQ

theorem logicallyEquivalent_trans {T : Set Proposition} {P Q R : Proposition}
    (hPQ : LogicallyEquivalentIn T P Q) (hQR : LogicallyEquivalentIn T Q R) :
    LogicallyEquivalentIn T P R := by
  unfold LogicallyEquivalentIn at *
  have pQ : T ⊢ implication P Q :=
    Ded.mp T (bicond P Q) (implication P Q)
      (deriv_conj_elim_left) hPQ
  have qP : T ⊢ implication Q P :=
    Ded.mp T (bicond P Q) (implication Q P)
      (deriv_conj_elim_right) hPQ
  have qR : T ⊢ implication Q R :=
    Ded.mp T (bicond Q R) (implication Q R)
      (deriv_conj_elim_left) hQR
  have rQ : T ⊢ implication R Q :=
    Ded.mp T (bicond Q R) (implication R Q)
      (deriv_conj_elim_right) hQR
  have pR : T ⊢ implication P R := imp_trans pQ qR
  have rP : T ⊢ implication R P := imp_trans rQ qP
  exact Ded.mp T (implication R P) (bicond P R)
    (Ded.mp T (implication P R) (implication (implication R P) (bicond P R))
      (deriv_conj_intro (P := implication P R) (Q := implication R P)) pR)
    rP

theorem logicallyEquivalent_equiv (T : Set Proposition) :
    Equivalence (LogicallyEquivalentIn T) := by
  refine ⟨logicallyEquivalent_refl T, ?_, ?_⟩
  · intro a b h; exact logicallyEquivalent_symm h
  · intro a b c h₁ h₂; exact logicallyEquivalent_trans h₁ h₂

end PropositionalLogic