import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Linarith
import AdmissiblePropLogic.Semantics

set_option linter.style.header false
set_option linter.style.whitespace false
set_option linter.style.longLine false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace PropositionalLogic

open Admissibility

-- ============================================================================
-- ## DNF and CNF
-- ============================================================================
--
-- A finite disjunction of finite conjunctions of *literals* is "disjunctive
-- normal form" (DNF); dually a finite conjunction of finite disjunctions of
-- literals is "conjunctive normal form" (CNF).  The main theorem says every
-- proposition is equivalent to one of each.  A machine wrote the words and a
-- proof assistant — which has no aesthetic opinion about normal forms at all —
-- has checked the proofs; one of those is real in a way that the other is not,
-- though both are true.
--
-- DESIGN (design rules D1/D2):
--  (D1) `bigConj`/`bigDisj` are **nonempty-only**: each is a fold over a
--       `(first, rest)` pair, so it always conjoins/disjoins at least its first
--       element.  There is NO `[] ↦ top` / `[] ↦ bot` base clause.
--  (D2) The degenerate cases are handled **by classification**, not by an empty
--       fold: a proposition with no variables is always true or always false
--       (`noVar_classify`), so it collapses to the literal
--       row `[[top]]` / `[[bot]]`.  The general branch follows a
--       truth-table sketch: enumerate the
--       assignments to the finitely many used variables, keep exactly the rows
--       on which the proposition is true (DNF) / false (CNF), and never leave a
--       row empty.
-- ============================================================================

-- ----------------------------------------------------------------------------
-- Literals, nonempty big conjunction / disjunction  (D1)
-- ----------------------------------------------------------------------------

-- A **literal** is `top`, `bot`, a propositional variable, or the negation of a
-- propositional variable.  Four cases; the machinery below will spend a
-- surprising amount of effort confirming that they stay that way.
def IsLiteral (L : Proposition) : Prop :=
  L = top ∨ L = bot ∨ (∃ n : ℕ, L = var n) ∨ (∃ n : ℕ, L = neg (var n))

-- Literal witnesses for the easy atoms (used throughout this section).
lemma isLiteral_var (n : ℕ) : IsLiteral (var n) := by
  unfold IsLiteral; right; right; left; exact ⟨n, rfl⟩
-- `¬P_n` is a literal (the negated-variable disjunct of `IsLiteral`).
lemma isLiteral_neg_var (n : ℕ) : IsLiteral (neg (var n)) := by
  unfold IsLiteral; right; right; right; exact ⟨n, rfl⟩
-- The two constants are literal rows `top` and `bot`.
lemma isLiteral_top : IsLiteral top := by unfold IsLiteral; simp
lemma isLiteral_bot : IsLiteral bot := by unfold IsLiteral; simp

-- Nonempty big conjunction over a `(first, rest)` fold.  Always has at least
-- one conjunct (its head) — design rule D1.  This is the left fold
-- `rest.foldl (fun acc b => conj acc b) first`, written recursively so that
-- the cons case reduces to `bigConj (conj first b) rest` definitionally.
-- (Refusing to define an empty conjunction saves us from deciding what nothing
-- means; see D2 for how the file gets away with it.)
def bigConj (first : Proposition) : List Proposition → Proposition
  | [] => first
  | b :: rest => bigConj (conj first b) rest

-- Nonempty big disjunction over a `(first, rest)` fold — the DNF outer layer.
def bigDisj (first : Proposition) : List Proposition → Proposition
  | [] => first
  | b :: rest => bigDisj (disj first b) rest

-- Evaluation of a big conjunction: true exactly when the head and every
-- element of `rest` are true.  The [simp]-target for all DNF work below.
theorem eval_bigConj (t : TruthAssignment) (first : Proposition) (rest : List Proposition) :
    eval t (bigConj first rest) = true ↔ eval t first = true ∧ ∀ x ∈ rest, eval t x = true := by
  induction rest generalizing first with
  | nil => simp [bigConj]
  | cons b bs ih =>
      simp only [bigConj]
      rw [ih (conj first b)]
      simp [eval_conj, Bool.and_eq_true, List.mem_cons, and_assoc]

-- Evaluation of a big disjunction: true when the head or some element of
-- `rest` is true — the DNF outer-layer [simp]-target.
theorem eval_bigDisj (t : TruthAssignment) (first : Proposition) (rest : List Proposition) :
    eval t (bigDisj first rest) = true ↔ eval t first = true ∨ ∃ x ∈ rest, eval t x = true := by
  induction rest generalizing first with
  | nil => simp [bigDisj]
  | cons b bs ih =>
      simp only [bigDisj]
      rw [ih (disj first b)]
      simp [eval_disj, Bool.or_eq_true, List.mem_cons, or_assoc]

-- Cons form of `eval_bigConj`: the head/rest split becomes one membership over
-- `first :: rest`.  Useful for reasoning about a row as a whole list.
theorem eval_bigConj_cons (t : TruthAssignment) (first : Proposition) (rest : List Proposition) :
    eval t (bigConj first rest) = true ↔ ∀ x ∈ first :: rest, eval t x = true := by
  rw [eval_bigConj]
  constructor
  · intro h b hb
    rw [List.mem_cons] at hb
    rcases hb with hb | hb
    · simpa [hb] using h.1
    · exact h.2 b hb
  · intro h
    constructor
    · exact h first (by simp)
    · intro b hb; exact h b (by simp [hb])

-- Cons form of `eval_bigDisj`: `∃ b ∈ first :: rest` with a true element.
theorem eval_bigDisj_cons (t : TruthAssignment) (first : Proposition) (rest : List Proposition) :
    eval t (bigDisj first rest) = true ↔ ∃ x ∈ first :: rest, eval t x = true := by
  rw [eval_bigDisj]
  constructor
  · intro h
    rcases h with h | ⟨b, hb, hh⟩
    · exact ⟨first, by simp, h⟩
    · exact ⟨b, by simp [hb], hh⟩
  · intro h
    rcases h with ⟨b, hb, hh⟩
    rw [List.mem_cons] at hb
    rcases hb with hb | hb
    · left; rw [hb] at hh; exact hh
    · right; exact ⟨b, hb, hh⟩

-- General helper for the CNF outer layer: a big conjunction over the list
-- `l` (head + tail) evaluated element-wise over `l`.
theorem eval_bigConj_of_list {α : Type} (t : TruthAssignment) (f : α → Proposition) (l : List α)
    (hne : l ≠ []) :
    eval t (bigConj (f (l.head hne)) (l.tail.map f)) = true ↔
      ∀ x ∈ l, eval t (f x) = true := by
  rw [eval_bigConj_cons]
  constructor
  · -- (→) H ranges over `f (head) :: (tail.map f)`.
    intro H x hx
    have hmem : f x ∈ f (l.head hne) :: l.tail.map f := by
      have hsplit : l.head hne :: l.tail = l := List.cons_head_tail hne
      rw [← hsplit] at hx
      rw [List.mem_cons] at hx
      rcases hx with hx | hx
      · rw [List.mem_cons]; left; exact congrArg f hx
      · rw [List.mem_cons]; right; exact List.mem_map.mpr ⟨x, hx, rfl⟩
    exact H (f x) hmem
  · -- (←) H : ∀ x ∈ l, eval t (f x) = true ; x ∈ head :: (tail.map f).
    intro H x0 hx0
    rw [List.mem_cons] at hx0
    rcases hx0 with hx0 | hx0r
    · simpa [hx0] using H (l.head hne) (List.head_mem hne)
    · rcases (List.mem_map.mp hx0r) with ⟨a, ha, rfl⟩
      exact H a (List.mem_of_mem_tail ha)

-- ----------------------------------------------------------------------------
-- UsedVars: finiteness, boundedness, and no-variable classification
-- ----------------------------------------------------------------------------

-- `UsedVars P` is finite: structurally, each connective only unions the
-- finitely many variable-sets of its subpropositions (D2 needs this finiteness).
-- Finiteness is the silent prerequisite of almost everything in this file.
set_option linter.flexible false in
theorem usedVars_finite (P : Proposition) : (UsedVars P).Finite := by
  induction P with
  | atom a ha =>
      cases a with
      | var n => simpa [UsedVars] using (Set.finite_singleton n)
      | _   => simp [Arity.arity] at ha
  | app a ha args ih =>
      cases a with
      | neg => simpa [UsedVars] using (ih ⟨0, ha⟩)
      | impl =>
          have h0 : (UsedVars (args ⟨0, ha⟩)).Finite := ih ⟨0, ha⟩
          have h1 : (UsedVars (args ⟨1, by decide⟩)).Finite := ih ⟨1, by decide⟩
          simpa [UsedVars] using (h0.union h1)
      | _ => simp [Arity.arity] at ha

-- `UsedVars P` is bounded: some `N` exceeds every variable of `P`.  This `N` is
-- the width of the truth-table slice used by the DNF/CNF construction.
set_option linter.flexible false in
theorem usedVars_bounded (P : Proposition) : ∃ N : ℕ, ∀ n ∈ UsedVars P, n < N := by
  induction P with
  | atom a ha =>
      cases a with
      | var n => refine ⟨n + 1, ?_⟩; intro m hm; simp [UsedVars] at hm; omega
      | _   => simp [Arity.arity] at ha
  | app a ha args ih =>
      cases a with
      | neg =>
          rcases (ih ⟨0, ha⟩) with ⟨N, hN⟩
          exact ⟨N, by intro m hm; exact hN m (by simpa [UsedVars] using hm)⟩
      | impl =>
          rcases (ih ⟨0, ha⟩) with ⟨N0, hN0⟩
          rcases (ih ⟨1, by decide⟩) with ⟨N1, hN1⟩
          refine ⟨max N0 N1, ?_⟩
          intro m hm
          rw [UsedVars] at hm
          cases hm with
          | inl h => exact lt_of_lt_of_le (hN0 m h) (Nat.le_max_left N0 N1)
          | inr h => exact lt_of_lt_of_le (hN1 m h) (Nat.le_max_right N0 N1)
      | _ => simp [Arity.arity] at ha

-- The bound from `usedVars_bounded` is positive whenever the proposition has a
-- variable: otherwise the (nonempty) used-var set could not be bounded below 1.
lemma bound_pos (P : Proposition) (h : UsedVars P ≠ ∅) : 0 < Classical.choose (usedVars_bounded P) := by
  have hspec := Classical.choose_spec (usedVars_bounded P)
  classical
  have hne : ∃ x : ℕ, x ∈ UsedVars P := by
    by_contra h0
    -- No variable occurs in `P`, so `UsedVars P` is empty, contradicting `h`.
    apply h
    apply Set.ext
    intro x
    constructor
    · intro hx; exfalso; exact h0 ⟨x, hx⟩
    · intro hx; simp at hx
  rcases hne with ⟨x, hx⟩
  exact Nat.lt_of_le_of_lt (Nat.zero_le x) (hspec x hx)

-- **Classification trick (design rule D2):** if `P` mentions no
-- variable, its value is independent of the assignment (by `eval_agrees_on_vars`),
-- so it is either always true (= `top`) or always false (= `bot`).
theorem noVar_classify (P : Proposition) (h : UsedVars P = ∅) :
    Equivalent P top ∨ Equivalent P bot := by
  classical
  by_cases hf : eval (fun _ : ℕ => true) P = true
  · left
    intro t
    have heg : ∀ n : ℕ, n ∈ UsedVars P → (fun _ : ℕ => true) n = t n := by
      intro n hn; rw [h] at hn; simp at hn
    rw [← eval_agrees_on_vars P heg, hf, eval_top]
  · right
    have hff : eval (fun _ : ℕ => true) P = false := Bool.eq_false_of_ne_true hf
    intro t
    have heg : ∀ n : ℕ, n ∈ UsedVars P → (fun _ : ℕ => true) n = t n := by
      intro n hn; rw [h] at hn; simp at hn
    rw [← eval_agrees_on_vars P heg, hff, eval_bot]

-- ----------------------------------------------------------------------------
-- Truth-table rows and the DNF construction
-- ----------------------------------------------------------------------------

-- Restrict a finite slice `s : Fin N → Bool` to a full truth assignment:
-- agree with `s` below `N`, false elsewhere.  A finite board, extended to the
-- infinite one with falsehood.
def restrictVec (N : ℕ) (s : Fin N → Bool) : TruthAssignment :=
  fun n => if h : n < N then s ⟨n, h⟩ else false

-- The DNF letters of a row: at index `i` we take `var i` if `s i` is true, else
-- `¬ var i`.  The row is the (nonempty) big conjunction of these letters.
-- `finRange N` is the ordered list `[0,1,...,N-1]`; its head is index 0.
lemma finRange_ne_nil {N : ℕ} (hN : 0 < N) : List.finRange N ≠ [] := by
  rw [← List.length_pos_iff]
  simpa [List.length_finRange] using hN

-- The head of the ordered list `finRange N` is index `0` (needed to split a
-- row's letters into `first :: rest`, per design D1).
lemma finRange_head {N : ℕ} (hN : 0 < N) :
    (List.finRange N).head (finRange_ne_nil hN) = ⟨0, hN⟩ := by
  cases N with
  | zero => simp at hN
  | succ n => simp [List.finRange_succ]

-- Mapping `f` over `finRange N` splits into the head letter (index 0) and the
-- letters of the tail.  This is how a row is a `(first, rest)` fold (D1).
lemma finRange_map_cons {α : Type} {N : ℕ} (hN : 0 < N) (f : Fin N → α) :
    (List.finRange N).map f = f ⟨0, hN⟩ :: ((List.finRange N).tail.map f) := by
  cases N with
  | zero => simp at hN
  | succ n =>
      rw [List.finRange_succ]
      simp [List.map_cons]

-- Head letter (index 0) and the remaining letters of a DNF row.
noncomputable def rowFirst (N : ℕ) (hN : 0 < N) (s : Fin N → Bool) : Proposition :=
  if s ⟨0, hN⟩ then var 0 else neg (var 0)

-- The tail letters of a DNF row: one letter per remaining variable, `var i` if
-- the assignment sets it, else `¬ var i`.
noncomputable def rowRest (N : ℕ) (_hN : 0 < N) (s : Fin N → Bool) : List Proposition :=
  (List.finRange N).tail.map (fun i : Fin N => if s i then var i.1 else neg (var i.1))

-- A DNF row: a nonempty big conjunction of one letter per used variable.
noncomputable def row (N : ℕ) (hN : 0 < N) (s : Fin N → Bool) : Proposition :=
  bigConj (rowFirst N hN s) (rowRest N hN s)

-- `rowFirst :: rowRest` is exactly the list of all letters of the row.
lemma row_cons {N : ℕ} (hN : 0 < N) (s : Fin N → Bool) :
    rowFirst N hN s :: rowRest N hN s =
      (List.finRange N).map (fun i : Fin N => if s i then var i.1 else neg (var i.1)) := by
  unfold rowFirst rowRest
  rw [← finRange_map_cons hN (fun i : Fin N => if s i then var i.1 else neg (var i.1))]

-- A DNF letter at index `i` is true under `t` iff `t` agrees with `s` at `i`.
lemma eval_rowLetter (s : Fin N → Bool) (t : TruthAssignment) (i : Fin N) :
    eval t (if s i then var i.1 else neg (var i.1)) = true ↔ t i.1 = s i := by
  cases h : s i <;> simp [h, eval_var, eval_neg]

-- Evaluation of a DNF row: true exactly when `t` agrees with `s` on every used
-- variable — i.e. the row "forces `t` to match `s`" (a bridge lemma).
theorem eval_row {N : ℕ} (hN : 0 < N) (s : Fin N → Bool) (t : TruthAssignment) :
    eval t (row N hN s) = true ↔ ∀ i : Fin N, t i.1 = s i := by
  unfold row
  rw [eval_bigConj_cons, row_cons]
  constructor
  · intro h i
    have : eval t ((fun i : Fin N => if s i then var i.1 else neg (var i.1)) i) = true :=
      h ((fun i : Fin N => if s i then var i.1 else neg (var i.1)) i)
        (by simpa [List.mem_map] using ⟨i, List.mem_finRange i, rfl⟩)
    exact (eval_rowLetter s t i).mp this
  · intro h b hb
    rcases (List.mem_map.mp hb) with ⟨a, ha, rfl⟩
    exact (eval_rowLetter s t a).mpr (h a)

-- The vectors on which `P` (restricted to the first `N` variables) is true.
noncomputable def satisfyingVecs (N : ℕ) (_hN : 0 < N) (P : Proposition) :
    Finset (Fin N → Bool) := by
  classical
  exact (Finset.univ : Finset (Fin N → Bool)).filter (fun s => eval (restrictVec N s) P = true)

-- A satisfying slice is present, so the slice list is nonempty.
theorem satisfyingVecs_ne (N : ℕ) (hN : 0 < N) (P : Proposition)
    (hsat : ∃ s : Fin N → Bool, eval (restrictVec N s) P = true) :
    (satisfyingVecs N hN P).toList ≠ [] := by
  classical
  rcases hsat with ⟨s, hs⟩
  have hmem : s ∈ (satisfyingVecs N hN P).toList :=
    Finset.mem_toList.mpr (by simp [satisfyingVecs, hs])
  rw [← List.length_pos_iff]
  exact List.length_pos_of_mem hmem

-- The big disjunction of the rows of all satisfying vectors (nonempty outer DNF).
noncomputable def disjOfRows (N : ℕ) (hN : 0 < N) (vs : List (Fin N → Bool)) (hne : vs ≠ []) :
    Proposition :=
  bigDisj (row N hN (vs.head hne)) (vs.tail.map (fun s => row N hN s))

-- Evaluation of the disjunction-of-rows: true iff some row in `vs` is true.
lemma eval_disjOfRows (N : ℕ) (hN : 0 < N) (vs : List (Fin N → Bool)) (hne : vs ≠ [])
    (t : TruthAssignment) :
    eval t (disjOfRows N hN vs hne) = true ↔ ∃ s ∈ vs, eval t (row N hN s) = true := by
  unfold disjOfRows
  rw [eval_bigDisj]
  constructor
  · intro h
    rcases h with h | h1
    · exact ⟨vs.head hne, List.head_mem hne, h⟩
    · rcases h1 with ⟨b, hb, hbrow⟩
      rcases (List.mem_map.mp hb) with ⟨s, hs, rfl⟩
      exact ⟨s, List.mem_of_mem_tail hs, hbrow⟩
  · intro h
    rcases h with ⟨s, hs, hsro⟩
    have hsplit : vs = vs.head hne :: vs.tail := (List.cons_head_tail hne).symm
    rw [hsplit] at hs
    rw [List.mem_cons] at hs
    rcases hs with hs' | hs'
    · left; simpa [hs'] using hsro
    · right
      refine ⟨row N hN s, ?_, hsro⟩
      exact List.mem_map.mpr ⟨s, hs', rfl⟩

-- The full DNF of `P` built over its satisfying vectors (general branch).
noncomputable def dnfRows {N : ℕ} (hN : 0 < N) (P : Proposition)
    (hsat : ∃ s : Fin N → Bool, eval (restrictVec N s) P = true) : Proposition :=
  disjOfRows N hN (satisfyingVecs N hN P).toList (satisfyingVecs_ne N hN P hsat)

-- If a row (for a satisfying vector) is true under `t`, then `t` agrees with
-- `restrictVec N s` on all used variables, so `eval t P` equals the row's truth.
lemma row_true_implies_eval {N : ℕ} (hN : 0 < N) (t : TruthAssignment) (s : Fin N → Bool)
    (P : Proposition) (hbound : ∀ n, n ∈ UsedVars P → n < N)
    (hrow : eval t (row N hN s) = true) (hsat : eval (restrictVec N s) P = true) :
    eval t P = true := by
  have hforce : ∀ i : Fin N, t i.1 = s i := (eval_row hN s t).mp hrow
  have hagree : ∀ n : ℕ, n ∈ UsedVars P → t n = (restrictVec N s) n := by
    intro n hn
    have hlt : n < N := hbound n hn
    have : t n = s ⟨n, hlt⟩ := by simpa using (hforce ⟨n, hlt⟩)
    simp [restrictVec, hlt, this]
  rw [eval_agrees_on_vars P hagree, hsat]

-- If `P` is true under `t`, its slice `s := fun i => t i.1` is a satisfying
-- vector whose row is true under `t` (hence appears in the DNF).
set_option linter.flexible false in
lemma eval_implies_some_row {N : ℕ} (hN : 0 < N) (P : Proposition)
    (hbound : ∀ n, n ∈ UsedVars P → n < N) (t : TruthAssignment) (hP : eval t P = true) :
    ∃ s ∈ (satisfyingVecs N hN P).toList, eval t (row N hN s) = true := by
  refine ⟨fun i => t i.1, ?mem, ?row⟩
  · exact Finset.mem_toList.mpr (by
      simp [satisfyingVecs]
      have hagree : ∀ n : ℕ, n ∈ UsedVars P → t n = (restrictVec N (fun i => t i.1)) n := by
        intro n hn
        have hlt : n < N := hbound n hn
        simp [restrictVec, hlt]
      rw [← eval_agrees_on_vars P hagree]
      exact hP)
  · exact (eval_row hN (fun i => t i.1) t).mpr (fun i => by simp)

-- The core equivalence: `eval t (dnfRows P) = true ↔ eval t P = true`.
theorem eval_dnfRows {N : ℕ} (hN : 0 < N) (P : Proposition)
    (hbound : ∀ n, n ∈ UsedVars P → n < N)
    (hsat : ∃ s : Fin N → Bool, eval (restrictVec N s) P = true) (t : TruthAssignment) :
    eval t (dnfRows hN P hsat) = true ↔ eval t P = true := by
  unfold dnfRows
  rw [eval_disjOfRows]
  constructor
  · rintro ⟨s, hs, hrow⟩
    have hsat' : eval (restrictVec N s) P = true := by
      simpa [satisfyingVecs, Finset.mem_filter, Finset.mem_univ] using (Finset.mem_toList.mp hs)
    exact row_true_implies_eval hN t s P hbound hrow hsat'
  · intro hP
    exact eval_implies_some_row hN P hbound t hP

-- A true-iff helper: for Boolean evaluations, `eval t Q = true ↔ eval t P = true`
-- implies the equality `eval t P = eval t Q`.
lemma equivalent_of_iff_true {P Q : Proposition} {t : TruthAssignment}
    (h : (eval t Q = true ↔ eval t P = true)) : eval t P = eval t Q := by
  by_cases hP : eval t P = true
  · have hQ : eval t Q = true := h.mpr hP
    rw [hP, hQ]
  · have hQf : eval t Q = false := by
      apply Bool.eq_false_of_ne_true
      intro hQ; exact hP (h.mp hQ)
    have hPf : eval t P = false := Bool.eq_false_of_ne_true hP
    rw [hPf, hQf]

-- ----------------------------------------------------------------------------
-- `InDNF` — DNF witnessed as a nonempty outer disjunction of nonempty
-- rows of literals.  (D1: every row and the outer layer nonempty.)
-- ----------------------------------------------------------------------------

-- `P` is in **disjunctive normal form** when it is equivalent to a nonempty
-- outer disjunction (`bigDisj`) of nonempty inner conjunctions (`bigConj`) of
-- literals.  The witness is split into a head `(first :: rest)` row and a list
-- of tail rows, matching the nonempty-fold design D1: there is never an empty
-- row or an empty outer disjunction.  The definition is verbose so the theorem
-- can be honest about what it builds.
def InDNF (P : Proposition) : Prop :=
  ∃ headRow : Proposition × List Proposition,
  ∃ tailRows : List (Proposition × List Proposition),
    Equivalent P
      (bigDisj (bigConj headRow.1 headRow.2) (tailRows.map (fun r => bigConj r.1 r.2))) ∧
    IsLiteral headRow.1 ∧ (∀ L ∈ headRow.2, IsLiteral L) ∧
    (∀ r ∈ tailRows, IsLiteral r.1 ∧ ∀ L ∈ r.2, IsLiteral L)

-- `top` and `bot` are in DNF via the single literal rows `[[top]]` / `[[bot]]`
-- (the degenerate examples); never an empty fold (design rule D2).
set_option linter.flexible false in
theorem InDNF_top : InDNF top := by
  unfold InDNF
  refine ⟨(top, []), [], ?_⟩
  simp [IsLiteral, Equivalent, bigConj, bigDisj]

-- `bot` is the single literal row `[[bot]]` — the degenerate contradiction case
-- of `InDNF` (design D2: a literal row, never an empty fold).
set_option linter.flexible false in
theorem InDNF_bot : InDNF bot := by
  unfold InDNF
  refine ⟨(bot, []), [], ?_⟩
  simp [IsLiteral, Equivalent, bigConj, bigDisj]

-- Example: `(P₀ and P₁) or (not P₁ and P₂)` is in disjunctive normal
-- form — the literal rows `[[var 0, var 1]]` and `[[neg (var 1), var 2]]`.
set_option linter.flexible false in
theorem example_dnf :
    InDNF (disj (conj (var 0) (var 1)) (conj (neg (var 1)) (var 2))) := by
  unfold InDNF
  refine ⟨(var 0, [var 1]), [(neg (var 1), [var 2])], ?_⟩
  constructor
  · simpa [bigConj, bigDisj, Equivalent] using
      (equivalent_refl (disj (conj (var 0) (var 1)) (conj (neg (var 1)) (var 2))))
  · constructor
    · exact isLiteral_var 0
    · constructor
      · intro L hL; simp [List.mem_cons] at hL; rcases hL; exact isLiteral_var 1
      · intro r hr; simp [List.mem_cons] at hr; rcases hr
        constructor
        · exact isLiteral_neg_var 1
        · intro L hL; simp [List.mem_cons] at hL; rcases hL; exact isLiteral_var 2

theorem example_top_dnf : InDNF top := InDNF_top
theorem example_bot_dnf : InDNF bot := InDNF_bot

-- Literal-ness of the DNF row components.
set_option linter.flexible false in
lemma isLiteral_rowFirst {N : ℕ} (hN : 0 < N) (s : Fin N → Bool) : IsLiteral (rowFirst N hN s) := by
  unfold rowFirst
  cases h : s ⟨0, hN⟩ <;> simp [h]
  · exact isLiteral_neg_var 0
  · exact isLiteral_var 0

-- A DNF letter at index `i` is a literal: `var i` if `s i` is set, else `neg (var i)`.
set_option linter.flexible false in
lemma isLiteral_rowLetter (s : Fin N → Bool) (i : Fin N) :
    IsLiteral (if s i then var i.1 else neg (var i.1)) := by
  cases h : s i <;> [simpa [h] using isLiteral_neg_var i.1; simpa [h] using isLiteral_var i.1]

-- Every letter in the tail of a DNF row is a literal.
lemma all_isLiteral_rowRest {N : ℕ} (hN : 0 < N) (s : Fin N → Bool) :
    ∀ L ∈ rowRest N hN s, IsLiteral L := by
  unfold rowRest
  intro L hL
  rcases (List.mem_map.mp hL) with ⟨i, hi, rfl⟩
  exact isLiteral_rowLetter s i

-- Every row of the tail dictionary is a `(head, row)` of literals — the DNF
-- witness for the tail rows of `InDNF` (`headRow` is a literal, each `row` is).
lemma all_isLiteral_tailRows {N : ℕ} (hN : 0 < N) (vs : List (Fin N → Bool)) :
    ∀ r ∈ vs.tail.map (fun s => (rowFirst N hN s, rowRest N hN s)),
      IsLiteral r.1 ∧ ∀ L ∈ r.2, IsLiteral L := by
  intro r hr
  rcases (List.mem_map.mp hr) with ⟨s, hs, rfl⟩
  constructor
  · exact isLiteral_rowFirst hN s
  · exact all_isLiteral_rowRest hN s

-- `disjOfRows` is in DNF with its natural `(rowFirst, rowRest)` witnesses.
theorem InDNF_disjOfRows {N : ℕ} (hN : 0 < N) (vs : List (Fin N → Bool)) (hne : vs ≠ []) :
    InDNF (disjOfRows N hN vs hne) := by
  unfold InDNF disjOfRows
  refine ⟨(rowFirst N hN (vs.head hne), rowRest N hN (vs.head hne)),
          vs.tail.map (fun s : Fin N → Bool => (rowFirst N hN s, rowRest N hN s)), ?_⟩
  constructor
  · simpa [disjOfRows, row, List.map_map, Function.comp_def] using (equivalent_refl (disjOfRows N hN vs hne))
  · constructor
    · exact isLiteral_rowFirst hN (vs.head hne)
    · constructor
      · exact all_isLiteral_rowRest hN (vs.head hne)
      · exact all_isLiteral_tailRows hN vs

-- `dnfRows` is in DNF.
theorem InDNF_dnfRows {N : ℕ} (hN : 0 < N) (P : Proposition)
    (hsat : ∃ s : Fin N → Bool, eval (restrictVec N s) P = true) : InDNF (dnfRows hN P hsat) := by
  unfold dnfRows
  exact InDNF_disjOfRows hN _ _

-- A non-contradiction is true on some assignment (used to seed the DNF slice).
lemma exists_satisfying_slice (P : Proposition) {N : ℕ} (_hN : 0 < N)
    (hbound : ∀ n, n ∈ UsedVars P → n < N) (hnotbot : ¬ Equivalent P bot) :
    ∃ s : Fin N → Bool, eval (restrictVec N s) P = true := by
  classical
  have hw : ∃ t : TruthAssignment, eval t P = true := by
    by_contra hn
    apply hnotbot
    intro t
    have ht : ¬ eval t P = true := fun h => hn ⟨t, h⟩
    have hfib : eval t P = false := Bool.eq_false_of_ne_true ht
    simp [hfib, eval_bot]
  rcases hw with ⟨t, ht⟩
  refine ⟨fun i => t i.1, ?_⟩
  have hagree : ∀ n : ℕ, n ∈ UsedVars P → t n = (restrictVec N (fun i => t i.1)) n := by
    intro n hn
    have hlt : n < N := hbound n hn
    simp [restrictVec, hlt]
  rw [← eval_agrees_on_vars P hagree]
  exact ht

-- The three-branch DNF construction (DNF half), which behaves the way a
-- beginner hopes it will — three cases, no hidden fourth:
--   • Contradiction          → the literal row `[[bot]]`;
--   • No variables, satisfiable → the literal row `[[top]]` (by `noVar_classify`);
--   • General (used vars)    → the disjunction of the satisfying rows over `Fin N`.
noncomputable def dnfOf (P : Proposition) : Proposition := by
  classical
  by_cases hc : Equivalent P bot
  · exact bot
  · by_cases hv : UsedVars P = ∅
    · exact top
    · let N : ℕ := Classical.choose (usedVars_bounded P)
      let hN : 0 < N := bound_pos P hv
      let hbound : ∀ n, n ∈ UsedVars P → n < N := Classical.choose_spec (usedVars_bounded P)
      let hsat : ∃ s : Fin N → Bool, eval (restrictVec N s) P = true :=
        exists_satisfying_slice P hN hbound hc
      exact dnfRows hN P hsat

-- `dnfOf` is always in DNF (each branch collapses to a nonempty literal row).
set_option linter.flexible false in
theorem InDNF_dnfOf (P : Proposition) : InDNF (dnfOf P) := by
  classical
  unfold dnfOf
  by_cases hc : Equivalent P bot
  · simp [hc]; exact InDNF_bot
  · by_cases hv : UsedVars P = ∅
    · simp [hc, hv]; exact InDNF_top
    · simp [hc, hv]
      let N : ℕ := Classical.choose (usedVars_bounded P)
      let hN : 0 < N := bound_pos P hv
      let hbound : ∀ n, n ∈ UsedVars P → n < N := Classical.choose_spec (usedVars_bounded P)
      let hsat : ∃ s : Fin N → Bool, eval (restrictVec N s) P = true :=
        exists_satisfying_slice P hN hbound hc
      change InDNF (dnfRows hN P hsat)
      exact InDNF_dnfRows hN P hsat

-- `P` is equivalent to its DNF (the heart of the DNF half; all the drama the
-- DNF side of this file permits unfolds here).
set_option linter.flexible false in
theorem equivalent_dnf (P : Proposition) : Equivalent P (dnfOf P) := by
  classical
  unfold dnfOf
  by_cases hc : Equivalent P bot
  · simp [hc]
  · by_cases hv : UsedVars P = ∅
    · simp [hc, hv]
      rcases (noVar_classify P hv) with htop | hbot
      · exact htop
      · exact False.elim (hc hbot)
    · simp [hc, hv]
      intro t
      let N : ℕ := Classical.choose (usedVars_bounded P)
      let hN : 0 < N := bound_pos P hv
      let hbound : ∀ n, n ∈ UsedVars P → n < N := Classical.choose_spec (usedVars_bounded P)
      let hsat : ∃ s : Fin N → Bool, eval (restrictVec N s) P = true :=
        exists_satisfying_slice P hN hbound hc
      change eval t P = eval t (dnfRows hN P hsat)
      exact equivalent_of_iff_true (eval_dnfRows hN P hbound hsat t)

-- Result (DNF half): every `P` is equivalent to a proposition in DNF.
theorem dnf_normal_form (P : Proposition) : ∃ Q : Proposition, InDNF Q ∧ Equivalent P Q :=
  ⟨dnfOf P, InDNF_dnfOf P, equivalent_dnf P⟩

-- ----------------------------------------------------------------------------
-- CNF construction (CNF half).  Dual to the DNF half:
-- rows for the **falsifying** vectors with the
-- **opposite** letters; outer layer is a nonempty conjunction.
-- ----------------------------------------------------------------------------

-- CNF head letter: `¬ var 0` if `s` sets it, else `var 0` (opposite of DNF).
noncomputable def cnfRowFirst (N : ℕ) (hN : 0 < N) (s : Fin N → Bool) : Proposition :=
  if s ⟨0, hN⟩ then neg (var 0) else var 0

-- The tail letters of a CNF row: `¬ var i` if `s` sets it, else `var i` — the
-- exact opposite of the DNF-tail letters (so a CNF row is true off `s`).
noncomputable def cnfRowRest (N : ℕ) (_hN : 0 < N) (s : Fin N → Bool) : List Proposition :=
  (List.finRange N).tail.map (fun i : Fin N => if s i then neg (var i.1) else var i.1)

-- A CNF row: a nonempty big disjunction of opposite letters.
noncomputable def cnfRow (N : ℕ) (hN : 0 < N) (s : Fin N → Bool) : Proposition :=
  bigDisj (cnfRowFirst N hN s) (cnfRowRest N hN s)

-- `cnfRowFirst :: cnfRowRest` is exactly the list of all letters of a CNF row
-- (the DNF analogue of `row_cons`, with the letters negated).
lemma cnfRow_cons {N : ℕ} (hN : 0 < N) (s : Fin N → Bool) :
    cnfRowFirst N hN s :: cnfRowRest N hN s =
      (List.finRange N).map (fun i : Fin N => if s i then neg (var i.1) else var i.1) := by
  unfold cnfRowFirst cnfRowRest
  rw [← finRange_map_cons hN (fun i : Fin N => if s i then neg (var i.1) else var i.1)]

-- A CNF letter at index `i` is true under `t` iff `t` differs from `s` at `i`.
set_option linter.flexible false in
lemma eval_cnfLetter (s : Fin N → Bool) (t : TruthAssignment) (i : Fin N) :
    eval t (if s i then neg (var i.1) else var i.1) = true ↔ t i.1 ≠ s i := by
  cases h : s i <;> simp [h, eval_neg, eval_var]

-- Evaluation of a CNF row: true exactly when `t` disagrees with `s` somewhere.
set_option linter.flexible false in
theorem eval_cnfRow {N : ℕ} (hN : 0 < N) (s : Fin N → Bool) (t : TruthAssignment) :
    eval t (cnfRow N hN s) = true ↔ ∃ i : Fin N, t i.1 ≠ s i := by
  unfold cnfRow
  rw [eval_bigDisj_cons, cnfRow_cons]
  constructor
  · rintro ⟨b, hb, hrow⟩
    rcases (List.mem_map.mp hb) with ⟨i, hi, rfl⟩
    exact ⟨i, (eval_cnfLetter s t i).mp hrow⟩
  · rintro ⟨i, hne⟩
    refine ⟨(fun i : Fin N => if s i then neg (var i.1) else var i.1) i, ?_, ?_⟩
    · simpa [List.mem_map] using ⟨i, List.mem_finRange i, rfl⟩
    · exact (eval_cnfLetter s t i).mpr hne

-- The vectors on which `P` (restricted to `N` variables) is false.
noncomputable def falsifyingVecs (N : ℕ) (_hN : 0 < N) (P : Proposition) :
    Finset (Fin N → Bool) := by
  classical
  exact (Finset.univ : Finset (Fin N → Bool)).filter (fun s => eval (restrictVec N s) P = false)

-- A falsifying slice exists, so the list of falsifying vectors is nonempty and
-- the nonempty outer CNF fold (D1) is well-formed.
theorem falsifyingVecs_ne (N : ℕ) (hN : 0 < N) (P : Proposition)
    (hfs : ∃ s : Fin N → Bool, eval (restrictVec N s) P = false) :
    (falsifyingVecs N hN P).toList ≠ [] := by
  classical
  rcases hfs with ⟨s, hs⟩
  have hmem : s ∈ (falsifyingVecs N hN P).toList :=
    Finset.mem_toList.mpr (by simp [falsifyingVecs, hs])
  rw [← List.length_pos_iff]
  exact List.length_pos_of_mem hmem

-- The big conjunction of the rows of all falsifying vectors (nonempty outer CNF).
noncomputable def cnfFromVecs (N : ℕ) (hN : 0 < N) (vs : List (Fin N → Bool)) (hne : vs ≠ []) :
    Proposition :=
  bigConj (cnfRow N hN (vs.head hne)) (vs.tail.map (fun s => cnfRow N hN s))

-- Evaluation of the conjunction-of-rows: true iff every row in `vs` is true.
lemma eval_cnfFromVecs (N : ℕ) (hN : 0 < N) (vs : List (Fin N → Bool)) (hne : vs ≠ [])
    (t : TruthAssignment) :
    eval t (cnfFromVecs N hN vs hne) = true ↔ ∀ s ∈ vs, eval t (cnfRow N hN s) = true := by
  unfold cnfFromVecs
  exact eval_bigConj_of_list t (fun s => cnfRow N hN s) vs hne

-- The full CNF of `P` built over its falsifying vectors (general branch).
noncomputable def cnfCore {N : ℕ} (hN : 0 < N) (P : Proposition)
    (hfs : ∃ s : Fin N → Bool, eval (restrictVec N s) P = false) : Proposition :=
  cnfFromVecs N hN (falsifyingVecs N hN P).toList (falsifyingVecs_ne N hN P hfs)

-- The slice of a false assignment is falsifying.
lemma exists_falsifying_slice_of_not_top (P : Proposition) {N : ℕ} (_hN : 0 < N)
    (hbound : ∀ n, n ∈ UsedVars P → n < N) (hnt : ¬ Equivalent P top) :
    ∃ s : Fin N → Bool, eval (restrictVec N s) P = false := by
  classical
  have hw : ∃ t : TruthAssignment, eval t P = false := by
    by_contra hn
    apply hnt
    intro t
    have ht : ¬ eval t P = false := fun h => hn ⟨t, h⟩
    have htT : eval t P = true := Bool.eq_true_of_ne_false ht
    simp [htT, eval_top]
  rcases hw with ⟨t, ht⟩
  refine ⟨fun i => t i.1, ?_⟩
  have hagree : ∀ n : ℕ, n ∈ UsedVars P → t n = (restrictVec N (fun i => t i.1)) n := by
    intro n hn
    have hlt : n < N := hbound n hn
    simp [restrictVec, hlt]
  rw [← eval_agrees_on_vars P hagree]
  exact ht

-- The core CNF equivalence: `eval t (cnfCore P) = true ↔ eval t P = true`.
-- A falsifying row is true under `t` iff `t` differs from its vector on some
-- used variable; so the CNF is true exactly when `t`'s own slice is not
-- falsifying, i.e. exactly when `P` is true under `t`.
set_option linter.flexible false in
theorem eval_cnfCore {N : ℕ} (hN : 0 < N) (P : Proposition)
    (hbound : ∀ n, n ∈ UsedVars P → n < N)
    (hfs : ∃ s : Fin N → Bool, eval (restrictVec N s) P = false) (t : TruthAssignment) :
    eval t (cnfCore hN P hfs) = true ↔ eval t P = true := by
  unfold cnfCore
  rw [eval_cnfFromVecs]
  constructor
  · intro hH
    by_contra hP'
    have hPf : eval t P = false := Bool.eq_false_of_ne_true hP'
    let u : Fin N → Bool := fun i => t i.1
    have uF : eval (restrictVec N u) P = false := by
      have hag : ∀ n : ℕ, n ∈ UsedVars P → t n = (restrictVec N u) n := by
        intro n hn; have hlt : n < N := hbound n hn; simp [restrictVec, u, hlt]
      rw [← eval_agrees_on_vars P hag, hPf]
    have hu_mem : u ∈ (falsifyingVecs N hN P).toList :=
      Finset.mem_toList.mpr (by simp [falsifyingVecs, uF])
    have hrow := hH u hu_mem
    have hne : ∃ i : Fin N, t i.1 ≠ u i := (eval_cnfRow hN u t).mp hrow
    rcases hne with ⟨i, hneq⟩
    exact hneq (by simp [u])
  · intro hP s hs
    have hsP : eval (restrictVec N s) P = false := by
      simpa [falsifyingVecs, Finset.mem_filter, Finset.mem_univ] using (Finset.mem_toList.mp hs)
    rw [eval_cnfRow]
    by_contra hn
    push Not at hn
    have hagree : ∀ n : ℕ, n ∈ UsedVars P → t n = (restrictVec N s) n := by
      intro n hn'
      have hlt : n < N := hbound n hn'
      have : t n = s ⟨n, hlt⟩ := by simpa using (hn ⟨n, hlt⟩)
      simp [restrictVec, hlt, this]
    have hfull : eval t P = eval (restrictVec N s) P := eval_agrees_on_vars P hagree
    rw [hfull, hsP] at hP
    simp at hP

-- The three-branch CNF construction (CNF half), the mirror image and equally
-- well-mannered:
--   • Tautology              → the literal row `[[top]]`;
--   • No variables, not top  → the literal row `[[bot]]` (by `noVar_classify`);
--   • General (used vars)    → the conjunction of the falsifying rows over `Fin N`.
noncomputable def cnfOf (P : Proposition) : Proposition := by
  classical
  by_cases ht : Equivalent P top
  · exact top
  · by_cases hv : UsedVars P = ∅
    · exact bot
    · let N : ℕ := Classical.choose (usedVars_bounded P)
      let hN : 0 < N := bound_pos P hv
      let hbound : ∀ n, n ∈ UsedVars P → n < N := Classical.choose_spec (usedVars_bounded P)
      let hfs : ∃ s : Fin N → Bool, eval (restrictVec N s) P = false :=
        exists_falsifying_slice_of_not_top P hN hbound ht
      exact cnfCore hN P hfs

-- ----------------------------------------------------------------------------
-- `InCNF` — CNF witnessed as a nonempty outer conjunction of nonempty
-- rows of literals.  (D1: every row and the outer layer nonempty.)
-- ----------------------------------------------------------------------------

-- `P` is in **conjunctive normal form** when it is equivalent to a nonempty
-- outer conjunction (`bigConj`) of nonempty inner disjunctions (`bigDisj`) of
-- literals — the exact dual of `InDNF` (D1: every row and the outer layer
-- nonempty).  The dual of the definition, which preserves the allergy to empty
-- folds.
def InCNF (P : Proposition) : Prop :=
  ∃ headRow : Proposition × List Proposition,
  ∃ tailRows : List (Proposition × List Proposition),
    Equivalent P
      (bigConj (bigDisj headRow.1 headRow.2) (tailRows.map (fun r => bigDisj r.1 r.2))) ∧
    IsLiteral headRow.1 ∧ (∀ L ∈ headRow.2, IsLiteral L) ∧
    (∀ r ∈ tailRows, IsLiteral r.1 ∧ ∀ L ∈ r.2, IsLiteral L)

-- `top` and `bot` are in CNF via the single literal rows `[[top]]` / `[[bot]]`
-- (the degenerate examples); never an empty fold (design rule D2).
set_option linter.flexible false in
theorem InCNF_top : InCNF top := by
  unfold InCNF
  refine ⟨(top, []), [], ?_⟩
  simp [IsLiteral, Equivalent, bigConj, bigDisj]

-- `bot` is the single literal row `[[bot]]` — the degenerate contradiction
-- case of `InCNF` (design D2).
set_option linter.flexible false in
theorem InCNF_bot : InCNF bot := by
  unfold InCNF
  refine ⟨(bot, []), [], ?_⟩
  simp [IsLiteral, Equivalent, bigConj, bigDisj]

theorem example_top_cnf : InCNF top := InCNF_top
theorem example_bot_cnf : InCNF bot := InCNF_bot

-- Literal-ness of the CNF row components.
set_option linter.flexible false in
lemma isLiteral_cnfRowFirst {N : ℕ} (hN : 0 < N) (s : Fin N → Bool) :
    IsLiteral (cnfRowFirst N hN s) := by
  unfold cnfRowFirst
  cases h : s ⟨0, hN⟩ <;> simp [h]
  · exact isLiteral_var 0
  · exact isLiteral_neg_var 0

set_option linter.flexible false in
-- A CNF letter at index `i` is a literal: `neg (var i)` if `s i` is set,
-- else `var i`.
lemma isLiteral_cnfLetter (s : Fin N → Bool) (i : Fin N) :
    IsLiteral (if s i then neg (var i.1) else var i.1) := by
  cases h : s i <;> [simpa [h] using isLiteral_var i.1; simpa [h] using isLiteral_neg_var i.1]

-- Every letter in the tail of a CNF row is a literal.
lemma all_isLiteral_cnfRowRest {N : ℕ} (hN : 0 < N) (s : Fin N → Bool) :
    ∀ L ∈ cnfRowRest N hN s, IsLiteral L := by
  unfold cnfRowRest
  intro L hL
  rcases (List.mem_map.mp hL) with ⟨i, hi, rfl⟩
  exact isLiteral_cnfLetter s i

-- Every row of the CNF tail dictionary is a `(head, row)` of literals — the
-- `InCNF` witness for the tail rows.
lemma all_isLiteral_cnfTailRows {N : ℕ} (hN : 0 < N) (vs : List (Fin N → Bool)) :
    ∀ r ∈ vs.tail.map (fun s => (cnfRowFirst N hN s, cnfRowRest N hN s)),
      IsLiteral r.1 ∧ ∀ L ∈ r.2, IsLiteral L := by
  intro r hr
  rcases (List.mem_map.mp hr) with ⟨s, hs, rfl⟩
  constructor
  · exact isLiteral_cnfRowFirst hN s
  · exact all_isLiteral_cnfRowRest hN s

-- `cnfFromVecs` is in CNF with its natural `(cnfRowFirst, cnfRowRest)` witnesses.
theorem InCNF_cnfFromVecs {N : ℕ} (hN : 0 < N) (vs : List (Fin N → Bool)) (hne : vs ≠ []) :
    InCNF (cnfFromVecs N hN vs hne) := by
  unfold InCNF cnfFromVecs
  refine ⟨(cnfRowFirst N hN (vs.head hne), cnfRowRest N hN (vs.head hne)),
          vs.tail.map (fun s : Fin N → Bool => (cnfRowFirst N hN s, cnfRowRest N hN s)), ?_⟩
  constructor
  · simpa [cnfFromVecs, cnfRow, List.map_map, Function.comp_def] using (equivalent_refl (cnfFromVecs N hN vs hne))
  · constructor
    · exact isLiteral_cnfRowFirst hN (vs.head hne)
    · constructor
      · exact all_isLiteral_cnfRowRest hN (vs.head hne)
      · exact all_isLiteral_cnfTailRows hN vs

-- `cnfCore` is in CNF.
theorem InCNF_cnfCore {N : ℕ} (hN : 0 < N) (P : Proposition)
    (hfs : ∃ s : Fin N → Bool, eval (restrictVec N s) P = false) : InCNF (cnfCore hN P hfs) := by
  unfold cnfCore
  exact InCNF_cnfFromVecs hN _ _

-- `cnfOf` is always in CNF (each branch collapses to a nonempty literal row).
set_option linter.flexible false in
theorem InCNF_cnfOf (P : Proposition) : InCNF (cnfOf P) := by
  classical
  unfold cnfOf
  by_cases ht : Equivalent P top
  · simp [ht]; exact InCNF_top
  · by_cases hv : UsedVars P = ∅
    · simp [ht, hv]; exact InCNF_bot
    · simp [ht, hv]
      let N : ℕ := Classical.choose (usedVars_bounded P)
      let hN : 0 < N := bound_pos P hv
      let hbound : ∀ n, n ∈ UsedVars P → n < N := Classical.choose_spec (usedVars_bounded P)
      let hfs : ∃ s : Fin N → Bool, eval (restrictVec N s) P = false :=
        exists_falsifying_slice_of_not_top P hN hbound ht
      change InCNF (cnfCore hN P hfs)
      exact InCNF_cnfCore hN P hfs

-- `P` is equivalent to its CNF (the heart of the CNF half) — the mirror image
-- of `equivalent_dnf`, argued clause-by-clause in the same patient way.
set_option linter.flexible false in
theorem equivalent_cnf (P : Proposition) : Equivalent P (cnfOf P) := by
  classical
  unfold cnfOf
  by_cases ht : Equivalent P top
  · simp [ht]
  · by_cases hv : UsedVars P = ∅
    · simp [ht, hv]
      rcases (noVar_classify P hv) with htop | hbot
      · exact False.elim (ht htop)
      · exact hbot
    · simp [ht, hv]
      intro t
      let N : ℕ := Classical.choose (usedVars_bounded P)
      let hN : 0 < N := bound_pos P hv
      let hbound : ∀ n, n ∈ UsedVars P → n < N := Classical.choose_spec (usedVars_bounded P)
      let hfs : ∃ s : Fin N → Bool, eval (restrictVec N s) P = false :=
        exists_falsifying_slice_of_not_top P hN hbound ht
      change eval t P = eval t (cnfCore hN P hfs)
      exact equivalent_of_iff_true (eval_cnfCore hN P hbound hfs t)

-- Result (CNF half): every `P` is equivalent to a proposition in CNF.
theorem cnf_normal_form (P : Proposition) : ∃ Q : Proposition, InCNF Q ∧ Equivalent P Q :=
  ⟨cnfOf P, InCNF_cnfOf P, equivalent_cnf P⟩

-- ----------------------------------------------------------------------------
-- Example: instantiate the main theorem on P₀ ↔ (P₁ ↔ P₂).
-- ----------------------------------------------------------------------------

-- Instantiate the DNF main theorems on a concrete proposition (rather than
-- computing its 8 rows by hand): `P₀ ↔ (P₁ ↔ P₂)` is equivalent to its
-- `dnfOf`, and that `dnfOf` is genuinely in DNF.  Left to the theorem rather
-- than the chalkboard, which is fairer to both.
theorem example_normal_form_abstract :
    InDNF (dnfOf (bicond (var 0) (bicond (var 1) (var 2)))) ∧
    Equivalent (bicond (var 0) (bicond (var 1) (var 2)))
      (dnfOf (bicond (var 0) (bicond (var 1) (var 2)))) :=
  ⟨InDNF_dnfOf (bicond (var 0) (bicond (var 1) (var 2))),
   equivalent_dnf (bicond (var 0) (bicond (var 1) (var 2)))⟩

end PropositionalLogic
