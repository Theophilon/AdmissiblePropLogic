import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Countable.Defs
import Mathlib.Data.List.Basic
import AdmissiblePropLogic.Soundness

set_option linter.style.header false
set_option linter.style.whitespace false
set_option linter.style.longLine false

namespace PropositionalLogic

open Admissibility

-- ============================================================================
-- ## Completeness
-- ============================================================================

--
-- This is the completeness section.  A language model wrote it; Lean, which is
-- not a member of the intended audience, has now verified every line of it.  The
-- definition of a complete theory, the "inconsistent ⇒ complete" exercise, and
-- the `Set.univ` half of the worked example are proved below.  So is the Henkin
-- lemma — every consistent theory extends to a complete consistent one, via the
-- finite-layer enumeration and a chain — and it drives the model-existence half
-- of Completeness through the truth-lemma machinery at the end of this file,
-- which also closes out the entailment-implies-provability half, a
-- compactness-style result, and `Complete Var`.  The whole completeness section
-- is proved; the proof assistant was not consulted on how it felt about that.

-- Definition — complete theory
-- Let T ⊆ Prop. We say that T is **complete** if for every P ∈ Prop, T ⊢ P or T ⊢ ¬ P.
-- A theory is **complete** when it decides every proposition: either the
-- proposition or its negation is provable from it.  Unfolding `Ded` and `neg`,
-- this is a pointwise disjunction of provability, which Lean parses as a plain
-- `∀ P, (T ⊢ P) ∨ (T ⊢ neg P)` and does not find dramatic.
def Complete (T : Set Proposition) : Prop :=
  ∀ P : Proposition, (T ⊢ P) ∨ (T ⊢ neg P)

-- Inconsistent ⇒ complete
-- Prove that if T is inconsistent, then T is complete.
-- An inconsistent theory proves `bot`; the ex-falso axiom scheme `efq` gives
-- `bot → P` for every `P`, and MP discharges it — so every proposition is
-- provable, making the definition's disjunction trivially true on the left.
-- Ex falso, and from that point nothing on the left is false.
theorem complete_of_inconsistent {T : Set Proposition} (h : Inconsistent T) : Complete T := by
  intro P
  left
  exact Ded.mp T bot P (Ded.efq T P) h

-- Which theories are (not) complete
-- Prop and Var are complete; while ∅ and {P₀} are not complete.
-- **`Prop` (the full theory `Set.univ`) is complete** — every
-- proposition belongs to it, so `T ⊢ P` holds by the `assm` rule and the
-- disjunction is again trivially true on the left.
theorem univ_complete : Complete (Set.univ : Set Proposition) := by
  intro P
  left
  exact Ded.assm (Set.univ : Set Proposition) P (by simp)

-- **Not complete:** `∅` and `{P₀}` require a *non-provability* argument
-- (`∅ ⊬ var 1`, `{P₀} ⊬ neg (var 1)`, …).  These follow from Soundness plus the
-- fact that the relevant proposition is not a tautology / not entailed, closing via a
-- handful of small semantic lemmas.
-- (Most theories are in fact not complete.  The ordinary ones stay classy
-- about it.)
--
-- **`Var` (the set of ALL propositional variables) is complete** —
-- `Var` is semantically the theory of the all-true assignment
-- `t ≡ true` (the only assignment satisfying every variable), so each proposition or
-- its negation is provable.  (Note `P₀ ∧ P₁` IS provable
-- from `Var`: `Var ⊢ P₀` and `Var ⊢ P₁` by `assm`, and `conj_intro` assembles
-- them.)
--
-- **`∅` is NOT complete**: instantiate the definition at the single
-- variable `var 0`.  Neither `∅ ⊢ var 0` nor `∅ ⊢ ¬(var 0)` can hold — the former
-- is refuted by the all-false assignment (where `var 0` is false), the latter by
-- the all-true assignment (where `¬(var 0)` is false).  `not_ded_of_not_entails`
-- (the contrapositive of Soundness, from `Soundness.lean`) turns those semantic
-- counter-assignments into non-provability.
theorem empty_not_complete : ¬ Complete (∅ : Set Proposition) := by
  intro hc
  rcases hc (var 0) with hleft | hright
  · have hne : ¬ Entails (∅ : Set Proposition) (var 0) := by
      intro hent
      have ht : eval (fun _ => false) (var 0) = true :=
        hent (fun _ => false) (by intro P hP; simp at hP)
      simp [eval_var] at ht
    exact (not_ded_of_not_entails hne) hleft
  · have hne : ¬ Entails (∅ : Set Proposition) (neg (var 0)) := by
      intro hent
      have ht : eval (fun _ => true) (neg (var 0)) = true :=
        hent (fun _ => true) (by intro P hP; simp at hP)
      simp [eval_neg, eval_var] at ht
    exact (not_ded_of_not_entails hne) hright

-- **`{P₀}` is NOT complete**: instantiate the definition at `var 1`.  The
-- assignment `t n = (n = 0)` satisfies `{P₀}` (so `P₀` is true) but makes
-- `var 1` false; the all-true assignment satisfies `{P₀}` but makes `¬(var 1)`
-- false.  Neither `{P₀} ⊢ var 1` nor `{P₀} ⊢ ¬(var 1)` is provable.
theorem singleton_not_complete : ¬ Complete ({var 0} : Set Proposition) := by
  intro hc
  rcases hc (var 1) with hleft | hright
  · have hne : ¬ Entails ({var 0} : Set Proposition) (var 1) := by
      intro hent
      let t : TruthAssignment := fun n => n == 0
      have hsat : Satisfies t ({var 0} : Set Proposition) := by
        intro P hP
        have hPeq : P = var 0 := by simpa using hP
        subst P
        simp [t, eval_var]
      have ht : eval t (var 1) = true := hent t hsat
      simp [t, eval_var] at ht
    exact (not_ded_of_not_entails hne) hleft
  · have hne : ¬ Entails ({var 0} : Set Proposition) (neg (var 1)) := by
      intro hent
      let t : TruthAssignment := fun _ => true
      have hsat : Satisfies t ({var 0} : Set Proposition) := by
        intro P hP
        have hPeq : P = var 0 := by simpa using hP
        subst P
        simp [t, eval_var]
      have ht : eval t (neg (var 1)) = true := hent t hsat
      simp [eval_neg, eval_var] at ht
    exact (not_ded_of_not_entails hne) hright

-- Henkin complete extension
-- If T is consistent, then there exists a complete consistent set T′ such that T ⊆ T′.
-- sketch : can be done without zorn?
-- 1. construct the enumeration of Propositions
--    - consider the set Λn of propositions with size less or equal to n and no proposition variable occurs except P0,...,Pn
--    - use cardinality to give function f_n
--    - let Q0 = ⊤, figure out l for Qk = fn(l)
-- 2. construct a chain Tn containing T with Qn ∈ T(n+1) or ¬Qn ∈ T(n+1) using recursion based on trivial consistency by cases of union
-- 3. The union of the chain will be the complete set we want

-- The finite-layer enumeration of the sketch.  The n-th layer is the set of
-- propositions of size at most `n` whose variables all lie among `P₀,...,P_n`;
-- every proposition belongs to some layer (so the layers give a surjection
-- `ℕ → Proposition`), and each layer is finite (its cardinality is bounded by
-- `(n + c)^n`, c = number of nullary/connective symbols).  Finiteness and the
-- surjection are realized concretely by `atoms`/`enum`/`every_prop_in_some_layer`
-- below.  No separate layer type is needed; the type system was already doing
-- enough bookkeeping.

-- ----------------------------------------------------------------------------
-- Countability of `Proposition`
-- ----------------------------------------------------------------------------
--
-- The Henkin construction below needs to *enumerate* every
-- proposition so it can build a chain that decides one proposition at a time.
-- That propositions are countable is not a design choice; it is a precondition,
-- and Mathlib declines to notice it on its own.  A finite-layer enumeration:
--
--   • `atoms k` — the finite set of atomic propositions using only `P₀..P_k`
--     (plus `top` and `bot`).
--   • `enum m k` — the set of propositions of *size ≤ m* whose variables all
--     lie among `P₀..P_k`, built by recursing on the size bound `m`: each step
--     adds one connective layer (`neg`/`conj`/`disj`) over the previous layer.
--   • `enum n n` is the *finite* `Finset` incarnation of the n-th layer (the
--     "each layer is finite" part), which is what we actually enumerate.
--   • `every_prop_in_some_layer` — `∀ P, ∃ n, P ∈ enum n n` (take `n` bigger
--     than both `size P` and every used variable of `P`; `maxVar` bounds the
--     used variables).
--   • `enumProp` — a surjection `ℕ → Proposition` that walks the (finitely
--     many) elements of the layers one triple `(m, i)` at a time via `Nat.pair`
--     / `Nat.unpair`.
--   • `instCountable` — `Countable Proposition` from that surjection via
--     `Function.Surjective.countable`.
--
-- This is exactly the sketch's "cardinality argument"; Mathlib does NOT
-- auto-derive `Countable` for `AdmissibleWord LogicalSymbol`, so we build it.

-- Atomic propositions with variable index ≤ k, plus `top` and `bot`.
noncomputable def atoms (k : ℕ) : Finset Proposition :=
  (Finset.range (k + 1)).image var ∪ ({top, bot} : Finset Proposition)

-- Two `atom` witnesses differing only in the arity proof are the same word.
lemma atom_eq {a : LogicalSymbol} {ha hb : Arity.arity a = 0} :
    (AdmissibleWord.atom a ha : Proposition) = AdmissibleWord.atom a hb := by
  apply congrArg (AdmissibleWord.atom a)
  exact Subsingleton.elim ha hb

-- `enum m k`: propositions of size ≤ m using only variables P₀..P_k.
noncomputable def enum : ℕ → ℕ → Finset Proposition
  | 0, _ => ∅
  | m + 1, k =>
      atoms k ∪
      (enum m k).image neg ∪
      ((enum m k) ×ˢ (enum m k)).image (fun p : Proposition × Proposition => conj p.1 p.2) ∪
      ((enum m k) ×ˢ (enum m k)).image (fun p : Proposition × Proposition => disj p.1 p.2)

-- The completeness direction: every proposition of size ≤ m with variables in
-- P₀..P_k is produced by `enum m k`.  Induction on the size bound `m`; each
-- connective case pushes the sub-proposition(s) (strictly smaller, so ≤ m) into
-- `enum m k` via the IH, then reassembles under the matching `image`.  (After
-- `cases P` the name `P` is gone, so every step names the reconstructed word.)
lemma enum_coverage : ∀ (m k : ℕ) (P : Proposition),
    size P ≤ m → (∀ j : ℕ, j ∈ UsedVars P → j ≤ k) → P ∈ enum m k := by
  intro m
  induction m with
  | zero =>
      intro k P hsize hv
      exact False.elim (by have hp : 0 < size P := size_pos P; omega)
  | succ m ih =>
      intro k P hsize hv
      cases P with
      | atom a ha =>
          cases a with
          | var n =>
              have hn : n ≤ k := hv n (by simp [UsedVars])
              have hinRange : n ∈ Finset.range (k + 1) := by simp [Nat.lt_succ_iff, hn]
              have hin : var n ∈ atoms k := by
                rw [atoms, Finset.mem_union]
                left
                exact Finset.mem_image.mpr ⟨n, by simpa using hinRange, rfl⟩
              have hPeq : AdmissibleWord.atom (LogicalSymbol.var n) ha = var n := by
                unfold var
                exact atom_eq (a := LogicalSymbol.var n)
              have hmem : AdmissibleWord.atom (LogicalSymbol.var n) ha ∈ atoms k := by
                simpa [hPeq] using hin
              simpa [enum] using (Or.inl hmem)
          | top =>
              have hin : top ∈ atoms k := by simp [atoms]
              have hPeq : AdmissibleWord.atom LogicalSymbol.top ha = top := by
                unfold top
                exact atom_eq (a := LogicalSymbol.top)
              have hmem : AdmissibleWord.atom LogicalSymbol.top ha ∈ atoms k := by
                simpa [hPeq] using hin
              simpa [enum] using (Or.inl hmem)
          | bot =>
              have hin : bot ∈ atoms k := by simp [atoms]
              have hPeq : AdmissibleWord.atom LogicalSymbol.bot ha = bot := by
                unfold bot
                exact atom_eq (a := LogicalSymbol.bot)
              have hmem : AdmissibleWord.atom LogicalSymbol.bot ha ∈ atoms k := by
                simpa [hPeq] using hin
              simpa [enum] using (Or.inl hmem)
          | neg => contradiction
          | conj => contradiction
          | disj => contradiction
      | app a ha args =>
          cases a with
          | var _ => simp [Arity.arity] at ha
          | top => simp [Arity.arity] at ha
          | bot => simp [Arity.arity] at ha
          | neg =>
              -- P = app .neg ha args = neg Q for the single sub-word Q.
              let Q : Proposition := args ⟨0, by decide⟩
              have hfeq : args = (fun _ : Fin (Arity.arity LogicalSymbol.neg) => Q) := by
                funext i
                rcases i with ⟨v, hv⟩
                change v < 1 at hv
                have hvz : v = 0 := by omega
                have hi : (⟨v, hv⟩ : Fin (Arity.arity LogicalSymbol.neg)) = ⟨0, by decide⟩ := by
                  apply Fin.ext
                  simp [hvz]
                rw [hi]
              have hPeq : AdmissibleWord.app LogicalSymbol.neg ha args = neg Q := by
                unfold neg
                rw [hfeq]
              have hs : size Q ≤ m := by
                have hlt : size Q < size (AdmissibleWord.app LogicalSymbol.neg ha args) :=
                  size_arg_lt _ ha args ⟨0, by decide⟩
                omega
              have hvQ : ∀ j, j ∈ UsedVars Q → j ≤ k := by
                intro j hj
                change j ∈ UsedVars (args ⟨0, by decide⟩) at hj
                exact hv j (by change j ∈ UsedVars (args ⟨0, by decide⟩); exact hj)
              have hQmem : Q ∈ enum m k := ih k Q hs hvQ
              have himg : neg Q ∈ (enum m k).image neg := Finset.mem_image.mpr ⟨Q, hQmem, rfl⟩
              have hen : neg Q ∈ enum (m + 1) k := by
                change neg Q ∈ atoms k ∪ (enum m k).image neg ∪
                  ((enum m k) ×ˢ (enum m k)).image (fun p : Proposition × Proposition => conj p.1 p.2) ∪
                  ((enum m k) ×ˢ (enum m k)).image (fun p : Proposition × Proposition => disj p.1 p.2)
                simp only [Finset.mem_union]
                left; left; right
                exact himg
              rw [hPeq]; exact hen
          | conj =>
              -- P = app .conj ha args = conj Q₁ Q₂ for the two coordinates.
              let Q₁ : Proposition := args ⟨0, by decide⟩
              let Q₂ : Proposition := args ⟨1, by decide⟩
              have hfeq : args = (fun i : Fin (Arity.arity LogicalSymbol.conj) => if i.val = 0 then Q₁ else Q₂) := by
                funext i
                rcases i with ⟨v, hv⟩
                change v < 2 at hv
                by_cases hz : v = 0
                · have hi : (⟨v, hv⟩ : Fin (Arity.arity LogicalSymbol.conj)) = ⟨0, by decide⟩ := by
                    apply Fin.ext; simpa using hz
                  rw [hi]; simp [Q₁]
                · have ho : v = 1 := by omega
                  have hi : (⟨v, hv⟩ : Fin (Arity.arity LogicalSymbol.conj)) = ⟨1, by decide⟩ := by
                    apply Fin.ext; simpa using ho
                  rw [hi]; simp [Q₂]
              have hPeq : AdmissibleWord.app LogicalSymbol.conj ha args = conj Q₁ Q₂ := by
                unfold conj
                rw [hfeq]
              have hs₁ : size Q₁ ≤ m := by
                have hlt : size Q₁ < size (AdmissibleWord.app LogicalSymbol.conj ha args) :=
                  size_arg_lt _ ha args ⟨0, by decide⟩
                omega
              have hs₂ : size Q₂ ≤ m := by
                have hlt : size Q₂ < size (AdmissibleWord.app LogicalSymbol.conj ha args) :=
                  size_arg_lt _ ha args ⟨1, by decide⟩
                omega
              have hv₁ : ∀ j, j ∈ UsedVars Q₁ → j ≤ k := by
                intro j hj
                change j ∈ UsedVars (args ⟨0, by decide⟩) at hj
                exact hv j (by
                  change j ∈ UsedVars (args ⟨0, by decide⟩) ∪ UsedVars (args ⟨1, by decide⟩)
                  exact Or.inl hj)
              have hv₂ : ∀ j, j ∈ UsedVars Q₂ → j ≤ k := by
                intro j hj
                change j ∈ UsedVars (args ⟨1, by decide⟩) at hj
                exact hv j (by
                  change j ∈ UsedVars (args ⟨0, by decide⟩) ∪ UsedVars (args ⟨1, by decide⟩)
                  exact Or.inr hj)
              have h₁ : Q₁ ∈ enum m k := ih k Q₁ hs₁ hv₁
              have h₂ : Q₂ ∈ enum m k := ih k Q₂ hs₂ hv₂
              have hprod : (Q₁, Q₂) ∈ (enum m k) ×ˢ (enum m k) :=
                Finset.mem_product.mpr ⟨h₁, h₂⟩
              have himg : conj Q₁ Q₂ ∈
                  ((enum m k) ×ˢ (enum m k)).image (fun pw : Proposition × Proposition => conj pw.1 pw.2) :=
                Finset.mem_image.mpr ⟨(Q₁, Q₂), hprod, rfl⟩
              have hen : conj Q₁ Q₂ ∈ enum (m + 1) k := by
                change conj Q₁ Q₂ ∈ atoms k ∪ (enum m k).image neg ∪
                  ((enum m k) ×ˢ (enum m k)).image (fun p : Proposition × Proposition => conj p.1 p.2) ∪
                  ((enum m k) ×ˢ (enum m k)).image (fun p : Proposition × Proposition => disj p.1 p.2)
                simp only [Finset.mem_union]
                left; right
                exact himg
              rw [hPeq]; exact hen
          | disj =>
              let Q₁ : Proposition := args ⟨0, by decide⟩
              let Q₂ : Proposition := args ⟨1, by decide⟩
              have hfeq : args = (fun i : Fin (Arity.arity LogicalSymbol.disj) => if i.val = 0 then Q₁ else Q₂) := by
                funext i
                rcases i with ⟨v, hv⟩
                change v < 2 at hv
                by_cases hz : v = 0
                · have hi : (⟨v, hv⟩ : Fin (Arity.arity LogicalSymbol.disj)) = ⟨0, by decide⟩ := by
                    apply Fin.ext; simpa using hz
                  rw [hi]; simp [Q₁]
                · have ho : v = 1 := by omega
                  have hi : (⟨v, hv⟩ : Fin (Arity.arity LogicalSymbol.disj)) = ⟨1, by decide⟩ := by
                    apply Fin.ext; simpa using ho
                  rw [hi]; simp [Q₂]
              have hPeq : AdmissibleWord.app LogicalSymbol.disj ha args = disj Q₁ Q₂ := by
                unfold disj
                rw [hfeq]
              have hs₁ : size Q₁ ≤ m := by
                have hlt : size Q₁ < size (AdmissibleWord.app LogicalSymbol.disj ha args) :=
                  size_arg_lt _ ha args ⟨0, by decide⟩
                omega
              have hs₂ : size Q₂ ≤ m := by
                have hlt : size Q₂ < size (AdmissibleWord.app LogicalSymbol.disj ha args) :=
                  size_arg_lt _ ha args ⟨1, by decide⟩
                omega
              have hv₁ : ∀ j, j ∈ UsedVars Q₁ → j ≤ k := by
                intro j hj
                change j ∈ UsedVars (args ⟨0, by decide⟩) at hj
                exact hv j (by
                  change j ∈ UsedVars (args ⟨0, by decide⟩) ∪ UsedVars (args ⟨1, by decide⟩)
                  exact Or.inl hj)
              have hv₂ : ∀ j, j ∈ UsedVars Q₂ → j ≤ k := by
                intro j hj
                change j ∈ UsedVars (args ⟨1, by decide⟩) at hj
                exact hv j (by
                  change j ∈ UsedVars (args ⟨0, by decide⟩) ∪ UsedVars (args ⟨1, by decide⟩)
                  exact Or.inr hj)
              have h₁ : Q₁ ∈ enum m k := ih k Q₁ hs₁ hv₁
              have h₂ : Q₂ ∈ enum m k := ih k Q₂ hs₂ hv₂
              have hprod : (Q₁, Q₂) ∈ (enum m k) ×ˢ (enum m k) :=
                Finset.mem_product.mpr ⟨h₁, h₂⟩
              have himg : disj Q₁ Q₂ ∈
                  ((enum m k) ×ˢ (enum m k)).image (fun pw : Proposition × Proposition => disj pw.1 pw.2) :=
                Finset.mem_image.mpr ⟨(Q₁, Q₂), hprod, rfl⟩
              have hen : disj Q₁ Q₂ ∈ enum (m + 1) k := by
                change disj Q₁ Q₂ ∈ atoms k ∪ (enum m k).image neg ∪
                  ((enum m k) ×ˢ (enum m k)).image (fun p : Proposition × Proposition => conj p.1 p.2) ∪
                  ((enum m k) ×ˢ (enum m k)).image (fun p : Proposition × Proposition => disj p.1 p.2)
                simp only [Finset.mem_union]
                right
                exact himg
              rw [hPeq]; exact hen

-- Largest variable index occurring in a proposition (0 for constants / none).
-- Recurses exactly like `UsedVars`, so it bounds `UsedVars P` from above.
def maxVar : Proposition → ℕ
  | .atom (.var n) _ => n
  | .atom _ _ => 0
  | .app .neg _ args => maxVar (args ⟨0, by decide⟩)
  | .app .conj _ args => max (maxVar (args ⟨0, by decide⟩)) (maxVar (args ⟨1, by decide⟩))
  | .app .disj _ args => max (maxVar (args ⟨0, by decide⟩)) (maxVar (args ⟨1, by decide⟩))
  | .app _ _ _ => 0

-- Every used variable of `P` is at most `maxVar P` — the finiteness/boundedness
-- of `UsedVars P` the surjection needs.  Structural induction mirroring
-- `UsedVars`/`eval_agrees_on_vars`.
theorem maxVar_bound : ∀ (P : Proposition) (j : ℕ), j ∈ UsedVars P → j ≤ maxVar P := by
  intro P
  induction P with
  | atom a ha =>
      intro j hj
      cases a with
      | var n =>
          have hjeq : j = n := by simpa [UsedVars] using hj
          subst j
          simp [maxVar]
      | top => simp [UsedVars] at hj
      | bot => simp [UsedVars] at hj
      | neg => simp [Arity.arity] at ha
      | conj => simp [Arity.arity] at ha
      | disj => simp [Arity.arity] at ha
  | app a ha args ih =>
      intro j hj
      cases a with
      | var _ => simp [Arity.arity] at ha
      | top => simp [Arity.arity] at ha
      | bot => simp [Arity.arity] at ha
      | neg =>
          have harg : j ∈ UsedVars (args ⟨0, by decide⟩) := by simpa [UsedVars] using hj
          simpa [maxVar] using (ih ⟨0, by decide⟩ j harg)
      | conj =>
          have harg : j ∈ UsedVars (args ⟨0, by decide⟩) ∪ UsedVars (args ⟨1, by decide⟩) := by
            simpa [UsedVars] using hj
          rcases harg with h0 | h1
          · have h : j ≤ maxVar (args ⟨0, by decide⟩) := ih ⟨0, by decide⟩ j h0
            exact le_trans h (by simp [maxVar])
          · have h : j ≤ maxVar (args ⟨1, by decide⟩) := ih ⟨1, by decide⟩ j h1
            change j ≤ max (maxVar (args ⟨0, by decide⟩)) (maxVar (args ⟨1, by decide⟩))
            exact le_trans h (le_max_right _ _)
      | disj =>
          have harg : j ∈ UsedVars (args ⟨0, by decide⟩) ∪ UsedVars (args ⟨1, by decide⟩) := by
            simpa [UsedVars] using hj
          rcases harg with h0 | h1
          · have h : j ≤ maxVar (args ⟨0, by decide⟩) := ih ⟨0, by decide⟩ j h0
            exact le_trans h (by simp [maxVar])
          · have h : j ≤ maxVar (args ⟨1, by decide⟩) := ih ⟨1, by decide⟩ j h1
            change j ≤ max (maxVar (args ⟨0, by decide⟩)) (maxVar (args ⟨1, by decide⟩))
            exact le_trans h (le_max_right _ _)

-- Every proposition belongs to some finite layer `enum n n`.
theorem every_prop_in_some_layer (P : Proposition) : ∃ n : ℕ, P ∈ enum n n := by
  refine ⟨max (size P) (maxVar P), ?_⟩
  exact enum_coverage _ _ P (le_max_left _ _) (by
    intro j hj
    exact le_trans (maxVar_bound P j hj) (le_max_right _ _))

-- The surjection `ℕ → Proposition`: at index `n`, decode `n = (m, i)` via the
-- Cantor-style pairing and pick the `i`-th element of layer `m`.
noncomputable def enumProp (n : ℕ) : Proposition :=
  let m := Nat.unpair n |>.1
  let i := Nat.unpair n |>.2
  if hi : i < (enum m m).toList.length then
    (enum m m).toList.get ⟨i, hi⟩
  else
    var 0

-- `enumProp` hits every proposition: given `P`, put it in layer
-- `m = max (size P) (maxVar P)`, recover its position `i` in that layer's list,
-- and re-encode `(m, i)` with `Nat.pair`.
theorem enumProp_surj : Function.Surjective enumProp := by
  intro P
  rcases every_prop_in_some_layer P with ⟨m, hm⟩
  have hmem : P ∈ (enum m m).toList := by simpa using hm
  rcases List.get_of_mem hmem with ⟨i, hi_eq⟩
  have hi_lt : i.val < (enum m m).toList.length := i.isLt
  refine ⟨Nat.pair m i.val, ?_⟩
  have hfd : Nat.unpair (Nat.pair m i.val) = (m, i.val) := by simp
  unfold enumProp
  rw [hfd]
  dsimp
  simp only [hi_lt]
  change (enum m m).toList.get i = P
  exact hi_eq

-- Countability: `Prop` is countable because it is the surjective image of `ℕ` —
-- an infinite object that still fits in a single index set, which is as
-- convenient as infiniteness ever gets here.
noncomputable instance instCountable : Countable Proposition :=
  Function.Surjective.countable enumProp_surj

-- ----------------------------------------------------------------------------
-- Henkin complete extension
-- ----------------------------------------------------------------------------
--
-- With `Countable Proposition` in hand we enumerate
-- every proposition `Q\2080, Q\2081, ...`, build a chain `T\2080=T ⊆ T\2081 ⊆ ...` where
-- `T_{n+1}` is `Tₙ` plus either `Qₙ` or `¬Qₙ` (whichever keeps the theory
-- consistent), and take the union.  This is the part of the proof that reads like
-- crossing a checkpoint: one decision per proposition, no appeal, and only
-- consistency to keep the whole thing from unraveling.  Two lemmas justify each
-- step:
--
--   • if `Tₙ ⊢ Qₙ`, adding `Qₙ` keeps consistency (the provability-consistency fact);
--   • otherwise `Tₙ ∪ {¬Qₙ}` is consistent, since the corresponding lemma says it
--     would be inconsistent exactly when `Tₙ ⊢ Qₙ`.
--
-- The union is consistent (`henkinUnion_consistent`, via the finite-subproof
-- argument: a proof of `bot` from the union uses finitely many hypotheses, all of
-- which live below some single `T_N`) and complete (`henkinUnion_complete`, each
-- `Qₙ` or `¬Qₙ` is decided by stage `n+1`).

-- The enumeration: reuse the surjection built in the Countable section above.
noncomputable def henkinEnum : ℕ → Proposition := enumProp

-- The Henkin step at one proposition `Q`: extend `Tn` by `Q` if `Tn ⊢ Q`
-- (consistent by a provability-consistency lemma), otherwise by `¬Q` (consistent via the
-- contrapositive of the negation lemma).
noncomputable def henkinStep (Tn : Set Proposition) (Q : Proposition) : Set Proposition := by
  classical
  exact if Tn ⊢ Q then Tn ∪ ({Q} : Set Proposition) else Tn ∪ ({neg Q} : Set Proposition)

-- The chain: `T\2080 = T`, `T_{n+1} = henkinStep (Tₙ) (Qₙ)`.
noncomputable def henkinChain (T : Set Proposition) : ℕ → Set Proposition
  | 0 => T
  | n + 1 => henkinStep (henkinChain T n) (henkinEnum n)

-- Each Henkin step preserves consistency.
lemma henkinStep_consistent {Tn : Set Proposition} {Q : Proposition} (h : Consistent Tn) :
    Consistent (henkinStep Tn Q) := by
  classical
  unfold henkinStep
  by_cases hQ : Tn ⊢ Q
  · rw [ite_eq_left hQ]
    exact inconsistent_add_of_provable h hQ
  · rw [ite_eq_right hQ]
    intro hincon
    have hq : Tn ⊢ Q := (provable_iff_inconsistent_neg).mpr hincon
    exact hQ hq

-- Consistency of every chain level, by induction along the chain.
lemma henkinChain_consistent {T : Set Proposition} (h : Consistent T) :
    ∀ n, Consistent (henkinChain T n) := by
  intro n
  induction n with
  | zero => exact h
  | succ n ih =>
      change Consistent (henkinStep (henkinChain T n) (henkinEnum n))
      exact henkinStep_consistent ih

-- The chain increases: `Tₙ ⊆ T_{n+1}` (both branches contain `Tₙ`).
lemma henkinChain_mono {T : Set Proposition} (n : ℕ) :
    henkinChain T n ⊆ henkinChain T (n + 1) := by
  intro x hx
  change x ∈ henkinStep (henkinChain T n) (henkinEnum n)
  classical
  unfold henkinStep
  by_cases h : henkinChain T n ⊢ henkinEnum n
  · simp [h, hx]
  · simp [h, hx]

-- Monotonicity over an offset: `Tᵢ ⊆ T_{i+k}`, by `k` applications of the step.
lemma henkinChain_le_of_add {T : Set Proposition} (i : ℕ) (k : ℕ) :
    henkinChain T i ⊆ henkinChain T (i + k) := by
  induction k with
  | zero => intro x hx; simpa using hx
  | succ k ih =>
      intro x hx
      exact henkinChain_mono (i + k) (ih hx)

-- Monotonicity across several steps.
lemma henkinChain_le {T : Set Proposition} {i j : ℕ} (hij : i ≤ j) :
    henkinChain T i ⊆ henkinChain T j := by
  have hk : j = i + (j - i) := by omega
  rw [hk]
  exact henkinChain_le_of_add (T := T) i (j - i)

-- The union of the whole chain.
def henkinUnion (T : Set Proposition) : Set Proposition :=
  {P | ∃ n : ℕ, P ∈ henkinChain T n}

-- A finite subset of the union is contained in a single chain level (take the
-- max of the finitely many levels providing its elements).  Compactness in
-- miniature: finitely many claims, each found finitely high up the chain.
lemma finite_subset_bounded {T T₀ : Set Proposition} (hfin : T₀.Finite)
    (h : ∀ a ∈ T₀, ∃ n : ℕ, a ∈ henkinChain T n) :
    ∃ N : ℕ, T₀ ⊆ henkinChain T N := by
  classical
  revert h
  refine @Set.Finite.induction_on Proposition
    (fun s _ => (∀ a ∈ s, ∃ n : ℕ, a ∈ henkinChain T n) → ∃ N : ℕ, s ⊆ henkinChain T N)
    T₀ hfin ?_ ?_
  · intro h
    exact ⟨0, by intro a ha; simp at ha⟩
  · intro a s ha hfs ih h
    have hs' : ∀ x, x ∈ s → ∃ n, x ∈ henkinChain T n := fun x hx => h x (by simp [hx])
    rcases ih hs' with ⟨N₀, hN₀⟩
    have ha' : ∃ n, a ∈ henkinChain T n := h a (by simp)
    rcases ha' with ⟨n_a, hna⟩
    refine ⟨max N₀ n_a, ?_⟩
    intro x hx
    rcases (by simpa using hx : x = a ∨ x ∈ s) with rfl | hxs
    · exact henkinChain_le (le_max_right N₀ n_a) hna
    · exact henkinChain_le (le_max_left N₀ n_a) (hN₀ hxs)

-- The union of a consistent chain is consistent: any proof of `bot` from the union
-- has a finite set of hypotheses, all below some `T_N`, contradicting that level's
-- consistency.
theorem henkinUnion_consistent {T : Set Proposition} (h : Consistent T) :
    Consistent (henkinUnion T) := by
  unfold Consistent
  intro hincon
  rcases consistent_of_finite_consistent hincon with ⟨T₀, hfin, hsub, hincon₀⟩
  rcases finite_subset_bounded hfin hsub with ⟨N, hN⟩
  exact (henkinChain_consistent h N) (weakening hN hincon₀)

-- Each `Qₙ` (or its negation) is decided by stage `n+1`.
lemma henkinChain_decides {T : Set Proposition} (n : ℕ) :
    henkinEnum n ∈ henkinChain T (n + 1) ∨ neg (henkinEnum n) ∈ henkinChain T (n + 1) := by
  change henkinEnum n ∈ henkinStep (henkinChain T n) (henkinEnum n) ∨
    neg (henkinEnum n) ∈ henkinStep (henkinChain T n) (henkinEnum n)
  classical
  unfold henkinStep
  by_cases h : henkinChain T n ⊢ henkinEnum n
  · left
    simp [h]
  · right
    simp [h]

-- The union is complete: every proposition (reachable as some `Qₙ`, by
-- surjectivity of the enumeration) is either in the union or its negation is.
lemma henkinUnion_complete {T : Set Proposition} : Complete (henkinUnion T) := by
  intro P
  rcases enumProp_surj P with ⟨m, hm⟩
  have hm' : henkinEnum m = P := by simpa [henkinEnum] using hm
  rcases (henkinChain_decides (T := T) m) with hq | hnq
  · left
    have hmem : henkinEnum m ∈ henkinUnion T := ⟨m + 1, hq⟩
    have hded : henkinUnion T ⊢ henkinEnum m := Ded.assm (henkinUnion T) (henkinEnum m) hmem
    simpa [hm'] using hded
  · right
    have hmem : neg (henkinEnum m) ∈ henkinUnion T := ⟨m + 1, hnq⟩
    have hded : henkinUnion T ⊢ neg (henkinEnum m) := Ded.assm (henkinUnion T) (neg (henkinEnum m)) hmem
    simpa [hm'] using hded

-- Henkin complete extension
-- Every consistent `T` extends to a complete consistent theory `T'.`
-- (A modest name for a result that does most of the work here; the lemma does
-- not mind.)
theorem henkin_complete_extension {T : Set Proposition} (h : Consistent T) :
    ∃ T', T ⊆ T' ∧ Complete T' ∧ Consistent T' := by
  refine ⟨henkinUnion T, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨0, by simpa [henkinChain] using hx⟩
  · exact henkinUnion_complete
  · exact henkinUnion_consistent h


-- ----------------------------------------------------------------------------
-- Model existence (the truth-lemma engine)
-- ----------------------------------------------------------------------------
--
-- To show every consistent `T` is satisfiable, take the complete consistent
-- extension `T'` from the Henkin lemma and read off a truth assignment from it:
-- `truthAssign T' n = true` iff `T' ⊢ var n`.  The semantics thus borrow their
-- opinion of each variable from what the complete theory proves.  The hard part —
-- the **truth lemma** — asserts by induction on `P` that a complete consistent
-- theory `Γ` *geometrically realizes* its own syntax:
--
--   eval (truthAssign Γ) P = true  ↔  Γ ⊢ P
--
-- In plainer words: the theory and its own model agree about everything, which a
-- semantics professor might call a coincidence, but which is a theorem here.
-- Each connective case is the corresponding deduction-theoretic fact about the
-- complete consistent `Γ`, factored as the three helper lemmas below:
--
--   • `complete_neg_iff` — `Γ⊢neg P ↔ ¬(Γ⊢P)`: completeness forces one of
--     `P`, `neg P` to be provable, consistency forbids both.
--   • `conj_ded_iff` — `Γ⊢conj P Q ↔ Γ⊢P ∧ Γ⊢Q` (conj_intro / conj_elim_left /
--     right, gluing via `Ded.mp`).
--   • `disj_ded_iff` — `Γ⊢disj P Q ↔ Γ⊢P ∨ Γ⊢Q`; the ← direction is the two
--     disjunction-intro schemes, the hard → direction is by contradiction
--     (both disjuncts unprovable ⇒ completeness supplies their negations ⇒ each
--     gives an implication to `bot` via `neg_imp` ⇒ `disj_elim` reaches `bot`,
--     contradicting consistency).
--
-- The variable base case reduces to `t n = true ↔ Γ ⊢ var n`, which is exactly
-- the definition of `truthAssign`.  `top` is always true (and provable via
-- `top_intro`); `bot` can never be true (and never provable, by consistency).
-- The assignment is defined by provability; whether that is profound or
-- circular, the induction does not care.
--
-- With the truth lemma, `Satisfies (truthAssign T') T` follows from the
-- inclusion `T ⊆ T'` of `henkin_complete_extension`: each `P ∈ T` lies in `T'`, hence is
-- provable, hence is true under the assignment.
--
-- **Note on entailment ⇒ provability** (`T ⊨ P ⇒ T ⊢ P`): it follows from model
-- existence by the contrapositive — if `T ⊬ P`, then `T ∪ {¬P}` is consistent
-- (by a consistency lemma), so some assignment satisfies it, making `P` false and
-- refuting `T ⊨ P`.  Non-provability, it turns out, is always witnessed; the
-- contrapositive makes sure of that.

-- The model-existence truth assignment: `truthAssign Γ n = true` iff `Γ ⊢ var n`.
-- This `t` decides variable `n` by provability (`t n = 1 iff T' ⊢ P_n`); noncomputable because
-- the `if` branches on provability, which needs a classical decidability witness.
-- A `def` that only exists in principle is still a `def`; Lean is a generous
-- employer.
noncomputable def truthAssign (Γ : Set Proposition) : TruthAssignment := by
  classical
  exact fun n : ℕ => if Γ ⊢ var n then true else false

-- Helper 1 (negation): for a complete consistent `Γ`, `neg P` is provable iff
-- `P` is not.  (→) since both `P` and `¬P` together would collapse to `bot`
-- (`inconsistent_of_both`); (←) by completeness, which decides `P` in `Γ`'s
-- favor only if `P` is actually provable.
lemma complete_neg_iff {Γ : Set Proposition} (hcmp : Complete Γ) (hcons : Consistent Γ)
    (P : Proposition) : (Γ ⊢ neg P) ↔ ¬ (Γ ⊢ P) := by
  constructor
  · intro hneg hP
    exact hcons (inconsistent_of_both hP hneg)
  · intro hnotP
    rcases hcmp P with hP | hneg
    · exact False.elim (hnotP hP)
    · exact hneg

-- Helper 2 (conjunction): `conj P Q` is provable iff both conjuncts are.  The (→)
-- direction projects with `conj_elim_left`/`right`; (←) assembles with
-- `conj_intro` (two `Ded.mp`s).
lemma conj_ded_iff {Γ : Set Proposition} {P Q : Proposition} :
    (Γ ⊢ conj P Q) ↔ ((Γ ⊢ P) ∧ (Γ ⊢ Q)) := by
  constructor
  · intro h
    constructor
    · exact Ded.mp Γ (conj P Q) P (Ded.conj_elim_left Γ P Q) h
    · exact Ded.mp Γ (conj P Q) Q (Ded.conj_elim_right Γ P Q) h
  · intro h
    rcases h with ⟨hP, hQ⟩
    exact Ded.mp Γ Q (conj P Q)
      (Ded.mp Γ P (implication Q (conj P Q)) (Ded.conj_intro Γ P Q) hP) hQ

-- Helper 3 (disjunction, → direction): from a provable `disj P Q` in a complete
-- consistent `Γ`, one of `P`, `Q` is provable.  By contradiction: if neither
-- were provable, completeness supplies `Γ⊢neg P` and `Γ⊢neg Q`; each gives an
-- implication to `bot` (`neg_imp`), and `disj_elim` on `disj P Q` reaches `bot`,
-- contradicting consistency.  (The genuinely semantic step in the truth lemma,
-- and where the model-existence theorem really happens.)
lemma disj_ded_of_ded {Γ : Set Proposition} (hcons : Consistent Γ) (hcmp : Complete Γ)
    {P Q : Proposition} (h : Γ ⊢ disj P Q) : (Γ ⊢ P) ∨ (Γ ⊢ Q) := by
  classical
  by_cases hP : Γ ⊢ P
  · exact Or.inl hP
  · by_cases hQ : Γ ⊢ Q
    · exact Or.inr hQ
    · exfalso
      have hnegP : Γ ⊢ neg P := by
        rcases hcmp P with hP' | hnegP
        · exact False.elim (hP hP')
        · exact hnegP
      have hnegQ : Γ ⊢ neg Q := by
        rcases hcmp Q with hQ' | hnegQ
        · exact False.elim (hQ hQ')
        · exact hnegQ
      have hPbot : Γ ⊢ implication P bot := neg_imp hnegP
      have hQbot : Γ ⊢ implication Q bot := neg_imp hnegQ
      have hstep : Γ ⊢ implication (disj P Q) bot :=
        Ded.mp Γ (implication Q bot) (implication (disj P Q) bot)
          (Ded.mp Γ (implication P bot)
            (implication (implication Q bot) (implication (disj P Q) bot))
            (Ded.disj_elim Γ P Q bot) hPbot)
          hQbot
      exact hcons (Ded.mp Γ (disj P Q) bot hstep h)

-- Helper 3': the full disjunction iff, bundling the two directions.
lemma disj_ded_iff {Γ : Set Proposition} (hcons : Consistent Γ) (hcmp : Complete Γ)
    {P Q : Proposition} : (Γ ⊢ disj P Q) ↔ ((Γ ⊢ P) ∨ (Γ ⊢ Q)) := by
  constructor
  · intro h; exact disj_ded_of_ded hcons hcmp h
  · intro h
    rcases h with hP | hQ
    · exact Ded.mp Γ P (disj P Q) (Ded.disj_intro_left Γ P Q) hP
    · exact Ded.mp Γ Q (disj P Q) (Ded.disj_intro_right Γ P Q) hQ

-- The truth lemma: for a complete consistent `Γ`, the assignment read off from
-- provability realizes every proposition exactly.  It is the centerpiece of the
-- file and receives rather more ceremony than the induction strictly requires.
-- Structural induction on `P`; the `neg`/`conj`/`disj` app cases rebuild the
-- canonical connective word (`hPeq`) exactly as `enum_coverage` does, then
-- reduce `eval` via the `eval_*` rules and each connective's deduction iff.
theorem truth_lemma {Γ : Set Proposition} (hcmp : Complete Γ) (hcons : Consistent Γ)
    (P : Proposition) : (eval (truthAssign Γ) P = true) ↔ Γ ⊢ P := by
  classical
  induction P with
  | atom a ha =>
      cases a with
      | var n =>
          have hvq : AdmissibleWord.atom (LogicalSymbol.var n) ha = var n := by
            unfold var
            exact atom_eq (a := LogicalSymbol.var n)
          rw [hvq]
          by_cases h : Γ ⊢ var n
          · simp [truthAssign, eval_var, h]
          · simp [truthAssign, eval_var, h]
      | top =>
          have htq : AdmissibleWord.atom LogicalSymbol.top ha = top := by
            unfold top
            exact atom_eq (a := LogicalSymbol.top)
          rw [htq]
          constructor
          · intro _; exact Ded.top_intro Γ
          · intro _; simp [eval_top]
      | bot =>
          have hbq : AdmissibleWord.atom LogicalSymbol.bot ha = bot := by
            unfold bot
            exact atom_eq (a := LogicalSymbol.bot)
          rw [hbq]
          constructor
          · intro ht; simp [eval_bot] at ht
          · intro hbot; exact False.elim (hcons hbot)
      | neg => simp [Arity.arity] at ha
      | conj => simp [Arity.arity] at ha
      | disj => simp [Arity.arity] at ha
  | app a ha args ih =>
      cases a with
      | var _ => simp [Arity.arity] at ha
      | top => simp [Arity.arity] at ha
      | bot => simp [Arity.arity] at ha
      | neg =>
          let Q : Proposition := args ⟨0, by decide⟩
          have hfeq : args = (fun _ : Fin (Arity.arity LogicalSymbol.neg) => Q) := by
            funext i
            rcases i with ⟨v, hv⟩
            change v < 1 at hv
            have hvz : v = 0 := by omega
            have hi : (⟨v, hv⟩ : Fin (Arity.arity LogicalSymbol.neg)) = ⟨0, by decide⟩ := by
              apply Fin.ext; simp [hvz]
            rw [hi]
          have hPeq : AdmissibleWord.app LogicalSymbol.neg ha args = neg Q := by
            unfold neg
            rw [hfeq]
          have ihQ := ih ⟨0, by decide⟩
          rw [hPeq]
          rw [complete_neg_iff hcmp hcons Q]
          rw [← ihQ]
          simp [eval_neg, Q]
      | conj =>
          let Q₁ : Proposition := args ⟨0, by decide⟩
          let Q₂ : Proposition := args ⟨1, by decide⟩
          have hfeq : args =
              (fun i : Fin (Arity.arity LogicalSymbol.conj) => if i.val = 0 then Q₁ else Q₂) := by
            funext i
            rcases i with ⟨v, hv⟩
            change v < 2 at hv
            by_cases hz : v = 0
            · have hi : (⟨v, hv⟩ : Fin (Arity.arity LogicalSymbol.conj)) = ⟨0, by decide⟩ := by
                apply Fin.ext; simpa using hz
              rw [hi]; simp [Q₁]
            · have ho : v = 1 := by omega
              have hi : (⟨v, hv⟩ : Fin (Arity.arity LogicalSymbol.conj)) = ⟨1, by decide⟩ := by
                apply Fin.ext; simpa using ho
              rw [hi]; simp [Q₂]
          have hPeq : AdmissibleWord.app LogicalSymbol.conj ha args = conj Q₁ Q₂ := by
            unfold conj
            rw [hfeq]
          have ihQ₁ := ih ⟨0, by decide⟩
          have ihQ₂ := ih ⟨1, by decide⟩
          rw [hPeq]
          rw [eval_conj]
          have hb : (eval (truthAssign Γ) Q₁ && eval (truthAssign Γ) Q₂) = true ↔
              (eval (truthAssign Γ) Q₁ = true ∧ eval (truthAssign Γ) Q₂ = true) := by
            cases eval (truthAssign Γ) Q₁ <;> cases eval (truthAssign Γ) Q₂ <;> simp
          rw [hb]
          rw [ihQ₁]
          rw [ihQ₂]
          exact conj_ded_iff.symm
      | disj =>
          let Q₁ : Proposition := args ⟨0, by decide⟩
          let Q₂ : Proposition := args ⟨1, by decide⟩
          have hfeq : args =
              (fun i : Fin (Arity.arity LogicalSymbol.disj) => if i.val = 0 then Q₁ else Q₂) := by
            funext i
            rcases i with ⟨v, hv⟩
            change v < 2 at hv
            by_cases hz : v = 0
            · have hi : (⟨v, hv⟩ : Fin (Arity.arity LogicalSymbol.disj)) = ⟨0, by decide⟩ := by
                apply Fin.ext; simpa using hz
              rw [hi]; simp [Q₁]
            · have ho : v = 1 := by omega
              have hi : (⟨v, hv⟩ : Fin (Arity.arity LogicalSymbol.disj)) = ⟨1, by decide⟩ := by
                apply Fin.ext; simpa using ho
              rw [hi]; simp [Q₂]
          have hPeq : AdmissibleWord.app LogicalSymbol.disj ha args = disj Q₁ Q₂ := by
            unfold disj
            rw [hfeq]
          have ihQ₁ := ih ⟨0, by decide⟩
          have ihQ₂ := ih ⟨1, by decide⟩
          rw [hPeq]
          rw [eval_disj]
          have hb : (eval (truthAssign Γ) Q₁ || eval (truthAssign Γ) Q₂) = true ↔
              (eval (truthAssign Γ) Q₁ = true ∨ eval (truthAssign Γ) Q₂ = true) := by
            cases eval (truthAssign Γ) Q₁ <;> cases eval (truthAssign Γ) Q₂ <;> simp
          rw [hb]
          rw [ihQ₁]
          rw [ihQ₂]
          exact (disj_ded_iff hcons hcmp).symm

-- Completeness Theorem
-- (1) For any proposition P if T ⊨ P, then T ⊢ P.
-- (2) If T is consistent, then T is satisfiable.
-- The two halves logicians always wanted to be the same theorem, and here they
-- are.  Model-existence half: extend `T` to a complete consistent theory `T'`
-- (Henkin lemma), evaluate at the assignment `truthAssign T'`, and use the truth
-- lemma to show that assignment satisfies `T` (via `T ⊆ T'`).  The
-- entailment-implies-provability half is the corollary `entailment_implies_deductible`.
theorem model_existence {T : Set Proposition} (hcons : Consistent T) : Satisfiable T := by
  rcases henkin_complete_extension hcons with ⟨T', hsub, hcmp, hcons'⟩
  refine ⟨truthAssign T', ?_⟩
  intro P hP
  have hP' : P ∈ T' := hsub hP
  exact (truth_lemma hcmp hcons' P).mpr (Ded.assm T' P hP')

-- ----------------------------------------------------------------------------
-- Entailment implies provability
-- ----------------------------------------------------------------------------
--
-- Part (1) is the contrapositive corollary of part (2): if `T ⊬ P`, then
-- `T ∪ {¬P}` is consistent (by `provable_iff_inconsistent_neg`), so model existence yields an
-- assignment satisfying it — which makes `¬P` true, hence `P` false — refuting
-- `T ⊨ P`.  Every missing derivation is still witnessed by a countermodel;
-- the contrapositive does the bookkeeping.
theorem entailment_implies_deductible {T : Set Proposition} {P : Proposition}
    (h : Entails T P) : T ⊢ P := by
  classical
  by_contra hnot
  have hcons : Consistent (T ∪ ({neg P} : Set Proposition)) := by
    unfold Consistent
    intro hincon
    exact hnot ((provable_iff_inconsistent_neg).mpr hincon)
  rcases model_existence hcons with ⟨t, hsat⟩
  have hsatT : Satisfies t T := by
    intro Q hQ
    exact hsat Q (Or.inl hQ)
  have htP : eval t P = true := h t hsatT
  have htneg : eval t (neg P) = true := hsat (neg P) (by simp)
  -- eval t (neg P) = !(eval t P) = !true = false, contradicting htneg.
  have hf : eval t (neg P) = false := by
    rw [eval_neg, htP]
    rfl
  rw [hf] at htneg
  simp at htneg

-- ----------------------------------------------------------------------------
-- A compactness-style result
-- ----------------------------------------------------------------------------
--
-- Compactness, obtained the honest way: a theorem rather than an axiom.
-- Hypothesis: every truth assignment makes *some* member of `T` true.
-- Conclusion: finitely many members already do — there is a finite `T₀ ⊆ T`
-- such that every assignment makes some member of `T₀` true (equivalently, the
-- big disjunction of `T₀`'s members is a tautology).
--
-- Proof (compactness via the negation theory): let `N = { neg Q | Q ∈ T }`.  The
-- hypothesis says `N` is NOT satisfiable (an assignment satisfying `N` would make
-- every member of `T` false).  By the contrapositive of model existence
-- (`model_existence`), `N` is inconsistent; by finite-subproof compactness
-- (`consistent_of_finite_consistent`) some finite `N₀ ⊆ N` proves `bot`.  Soundness then says
-- `N₀` is unsatisfiable, so each assignment falsifies some `neg Q ∈ N₀`, hence
-- satisfies the corresponding `Q`; those `Q`'s form the finite `T₀`.

-- Choice of a member `Q ∈ T` witnessing `neg Q = P` (defaults to `top` when no
-- witness exists).  `noncomputable` because the `if`/`Classical.choose` branch on
-- an existential, which needs a classical `Decidable` instance.
noncomputable def negPreimageQ (T : Set Proposition) (P : Proposition) : Proposition := by
  classical
  exact if h : ∃ Q : Proposition, Q ∈ T ∧ neg Q = P then Classical.choose h else top

-- The chosen member is indeed in `T`, and its negation is exactly `P`.
lemma negPreimage_spec {T : Set Proposition} {P : Proposition}
    (hN : ∃ Q : Proposition, Q ∈ T ∧ neg Q = P) :
    negPreimageQ T P ∈ T ∧ neg (negPreimageQ T P) = P := by
  have hred : negPreimageQ T P = Classical.choose hN := by
    unfold negPreimageQ
    exact dite_eq_left hN
  rw [hred]
  exact Classical.choose_spec hN

-- Bool helpers used below, stated with the named function `Bool.not` so we never
-- write the `!`-notation inside a goal (it binds looser than `=`, which would
-- change the parse of `!b = true`).
-- `¬(b = true)` forces `b = false` (Bool is two-valued).
lemma bool_ne_true_to_false (b : Bool) (h : ¬(b = true)) : b = false := by
  cases b <;> simp at h ⊢
-- `Bool.not b = false` iff `b = true`.
lemma bool_not_eq_false (b : Bool) : (Bool.not b = false) ↔ b = true := by
  cases b <;> simp

-- The conclusion is expressed with a finite subset `T₀ ⊆ T`
-- whose members are "covered by truth" at every assignment (i.e. their big
-- disjunction is a tautology).
theorem finite_subset_pointwise_true {T : Set Proposition}
    (h : ∀ t : TruthAssignment, ∃ Q, Q ∈ T ∧ eval t Q = true) :
    ∃ T₀ : Set Proposition, T₀.Finite ∧ T₀ ⊆ T ∧
      (∀ t : TruthAssignment, ∃ Q, Q ∈ T₀ ∧ eval t Q = true) := by
  classical
  -- N = { neg Q | Q ∈ T }: the theory of negated members.
  let N : Set Proposition := {P | ∃ Q, Q ∈ T ∧ neg Q = P}
  -- N is not satisfiable: an assignment satisfying N makes every member of T false.
  have hN : ¬ Satisfiable N := by
    intro hs
    rcases hs with ⟨t, hsat⟩
    rcases h t with ⟨Q, hQ, htQ⟩
    have hnegmem : neg Q ∈ N := ⟨Q, hQ, rfl⟩
    have htneg : eval t (neg Q) = true := hsat (neg Q) hnegmem
    have hf : eval t (neg Q) = false := by
      rw [eval_neg, htQ]
      rfl
    rw [hf] at htneg
    simp at htneg
  -- Contrapositive of model existence: N is inconsistent.
  have hinc : Inconsistent N := by
    by_contra hnot
    exact hN (model_existence hnot)
  -- Finite inconsistent subtheory (compactness of the derivation relation).
  rcases consistent_of_finite_consistent hinc with ⟨N₀, hN₀fin, hN₀sub, hN₀inc⟩
  -- T₀ = the chosen members witnessing each element of N₀.
  let T₀ : Set Proposition := (fun P => negPreimageQ T P) '' N₀
  refine ⟨T₀, ?_, ?_, ?_⟩
  · -- T₀ is finite (the image of the finite N₀).
    exact hN₀fin.image (fun P => negPreimageQ T P)
  · -- T₀ ⊆ T: each chosen witness is a member of T.
    intro Q hQ
    rcases hQ with ⟨P, hP, hg⟩
    have hP' : P ∈ N := hN₀sub hP
    rcases hP' with ⟨R, hR, hPeq⟩
    have hspec := negPreimage_spec ⟨R, hR, hPeq⟩
    rw [← hg]
    exact hspec.1
  · -- Every assignment is "covered" by T₀: it satisfies some member of T₀.
    intro t
    -- N₀ ⊢ bot, so by soundness N₀ is unsatisfiable at t.
    have hsat' : ¬ Satisfies t N₀ := by
      intro hs
      have hent : eval t bot = true := soundness hN₀inc t hs
      simp [eval_bot] at hent
    -- Hence some member P ∈ N₀ is false under t.
    have hex : ∃ P, P ∈ N₀ ∧ eval t P = false := by
      by_contra hno
      apply hsat'
      intro P hP
      by_cases hb : eval t P = true
      · exact hb
      · exfalso
        exact hno ⟨P, hP, bool_ne_true_to_false _ hb⟩
    rcases hex with ⟨P, hP, hPf⟩
    have hPn : P ∈ N := hN₀sub hP
    rcases hPn with ⟨R, hR, hPeq⟩
    have hspec := negPreimage_spec ⟨R, hR, hPeq⟩
    let Q : Proposition := negPreimageQ T P
    refine ⟨Q, ?_, ?_⟩
    · -- Q ∈ T₀ (P is the preimage of Q under the choice function).
      exact ⟨P, hP, rfl⟩
    · -- eval t Q = true: P = neg Q is false, so Q is true.
      have he : eval t (neg Q) = false := by
        change eval t (neg (negPreimageQ T P)) = false
        rw [hspec.2]
        exact hPf
      have htQ : eval t Q = true := by
        have hnb : Bool.not (eval t Q) = false := by
          simpa [eval_neg] using he
        exact (bool_not_eq_false (eval t Q)).mp hnb
      exact htQ

-- ----------------------------------------------------------------------------
-- Example — `Var` is complete
-- ----------------------------------------------------------------------------
--
-- `Var` is the theory of all propositional variables.  It is satisfied by exactly
-- the all-true assignment `t ≡ true`, so by the Completeness Theorem (part (1))
-- every `P` or `¬P` is provable from `Var`, i.e. `Complete Var`.  A model with
-- one assignment leaves little to the imagination, which is the point.
def Var : Set Proposition := {P | ∃ n : ℕ, P = var n}

-- `Var` is complete.  The only assignment satisfying
-- `Var` is the all-true one, `t ≡ true`; under it every proposition evaluates to a
-- Bool value `P (true, true, …)`, which is either `true` or `false`.  The
-- two halves of completeness fall out by evaluating under that single assignment
-- and using decidability — whichever way `P` evaluates, either it or its
-- negation holds in the model, and completeness (entailment ⇒ provability)
-- transfers that back to a derivation.  The theorem is effectively polarizing
-- every proposition against a single fixed endpoint.
theorem complete_var : Complete Var := by
  classical
  intro P
  by_cases hP : eval (fun _ : ℕ => true) P = true
  · left
    exact entailment_implies_deductible (fun t hsat => by
      have ht : t = (fun _ : ℕ => true) := by
        funext n
        simpa [eval_var] using (hsat (var n) ⟨n, rfl⟩)
      rw [ht]
      exact hP)
  · right
    have hnegP : eval (fun _ : ℕ => true) (neg P) = true := by
      rw [eval_neg]
      have hPfalse : eval (fun _ : ℕ => true) P = false := bool_ne_true_to_false _ hP
      simp [hPfalse]
    exact entailment_implies_deductible (fun t hsat => by
      have ht : t = (fun _ : ℕ => true) := by
        funext n
        simpa [eval_var] using (hsat (var n) ⟨n, rfl⟩)
      rw [ht]
      exact hnegP)

end PropositionalLogic
