import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic
import Mathlib.Logic.Encodable.Basic
import Mathlib.Logic.Equiv.List
import Mathlib.Tactic.Basic
import Mathlib.Order.WellFounded
import AdmissiblePropLogic.AdmissibleWord

set_option linter.style.header false
set_option linter.style.whitespace false
set_option linter.style.longLine false

namespace PropositionalLogic

universe u

open Admissibility


-- ============================================================================
-- ## Propositions

-- ============================================================================
-- ----------------------------------------------------------------------------
-- Alphabet and arity

-- ----------------------------------------------------------------------------
-- The alphabet of propositional logic: a countable
-- supply of propositional variables `P_n` together with the five connectives
-- `top`, `bot`, `neg`, `conj`, `disj`.  A single inductive type with a `var n`
-- constructor stands in for the set `Var ∪ {top, bot, not, and, or}`.
-- A union of finitely many things has a certain charm; an inductive type,
inductive LogicalSymbol where
  | var  : Nat → LogicalSymbol
  | top
  | bot
  | neg
  | conj
  | disj
  deriving DecidableEq, Repr

-- however, actually exists.
-- The arity function of the alphabet:
-- variables and the two constants have arity `0`, negation has arity `1`, and
-- conjunction/disjunction have arity `2`.  Feeding this to `AdmissibleWord`
-- makes "proposition" mean "well-formed against these arities". The term was
instance : Arity LogicalSymbol where
  arity
    | .var _   => 0
    | .top     => 0
    | .bot     => 0
    | .neg     => 1
    | .conj    => 2
    | .disj    => 2

-- chosen by a machine; `AdmissibleWord` is the part Lean actually believes.
-- ----------------------------------------------------------------------------
-- Propositions and the convenience constructors

-- ----------------------------------------------------------------------------
-- A **proposition** is an admissible word over the logical symbols:
-- `AdmissibleWord LogicalSymbol` with the arity instance
-- above supplies well-formedness for free. "For free" being the only price
abbrev Proposition := AdmissibleWord LogicalSymbol

-- this project's definitions ever agree to charge.
-- The five convenience constructors in Polish-notation order.  Each builds the
-- corresponding `AdmissibleWord` node with its arity witness discharged by
-- `rfl`/`decide`, so callers never mention those proofs. The witnesses exist;
-- whether anyone reads them is a question the proofs pointedly decline.
def var (n : Nat) : Proposition := .atom (.var n) rfl
--   `var n`   = Pₙ, the n-th propositional variable.
def top : Proposition := .atom .top rfl
--   `top`     = the truth constant ⊤.
def bot : Proposition := .atom .bot rfl
--   `bot`     = the falsity constant ⊥.
def neg (p : Proposition) : Proposition := .app .neg (by decide) (fun _ => p)
--   `neg P`   = ¬ P.
def conj (p q : Proposition) : Proposition := .app .conj (by decide) (fun i => if i.val = 0 then p else q)
--   `conj p q`= p ∧ q, with the two sub-words picked out by their index.
def disj (p q : Proposition) : Proposition := .app .disj (by decide) (fun i => if i.val = 0 then p else q)

--   `disj p q`= p ∨ q, with the two sub-words picked out by their index.
-- ----------------------------------------------------------------------------
-- Unique decomposition of connective nodes

-- ----------------------------------------------------------------------------
-- GENERIC: constructor injectivity recovers the args-set for a fixed head.
-- Equality of two nodes, opened along the seam, returns equality of their
lemma app_args_inj (s : LogicalSymbol) {ha hb : Arity.arity s > 0}
    {f g : Fin (Arity.arity s) → Proposition}
    (h : AdmissibleWord.app s ha f = AdmissibleWord.app s hb g) : f = g := by
  cases h; rfl

-- argument lists. Nothing glamorous; the arguments are simply where it all is.
lemma arg1_const (f : Fin (Arity.arity LogicalSymbol.neg) → Proposition) :
    ∃! Q : Proposition, f = (fun _ => Q) := by
  refine ⟨f ⟨0, by decide⟩, ?_, ?_⟩
  · funext i; rcases i with ⟨v, hv⟩
    change v < 1 at hv
    have hi : (⟨v, hv⟩ : Fin (Arity.arity LogicalSymbol.neg)) = ⟨0, by decide⟩ := by congr 1; omega
    rw [hi]
  · intro Q' h'; exact (congrFun h' ⟨0, by decide⟩).symm

-- An arity-1 args-set is constant on its (unique) argument.
lemma arg2_cond (c : LogicalSymbol) (hc : Arity.arity c = 2)
    (f : Fin (Arity.arity c) → Proposition) (p q : Proposition) :
    f = (fun i : Fin (Arity.arity c) => if i.val = 0 then p else q) ↔
      f ⟨0, by simp [hc]⟩ = p ∧ f ⟨1, by simp [hc]⟩ = q := by
  constructor
  · intro h; constructor <;> (rw [h]; simp)
  · intro h; rcases h with ⟨h0, h1⟩; funext i; rcases i with ⟨v, hv⟩
    have hv2 : v < 2 := by simpa [hc] using hv
    by_cases hz : v = 0
    · have hi : (⟨v, hv⟩ : Fin (Arity.arity c)) = ⟨0, by simp [hc]⟩ := by apply Fin.ext; simpa using hz
      rw [hi]; simpa using h0
    · have ho : v = 1 := by omega
      have hi : (⟨v, hv⟩ : Fin (Arity.arity c)) = ⟨1, by simp [hc]⟩ := by apply Fin.ext; simpa using ho
      rw [hi]; simpa using h1

-- An arity-2 args-set equals the (p,q)-conditional iff its two co-ordinates are p,q.
lemma unary_unique (H : Arity.arity LogicalSymbol.neg > 0)
    (f : Fin (Arity.arity LogicalSymbol.neg) → Proposition) :
    ∃! Q, AdmissibleWord.app LogicalSymbol.neg H f = neg Q := by
  rcases arg1_const f with ⟨Q, hQ, huniq⟩
  refine ⟨Q, ?_, ?_⟩
  · rw [hQ]; unfold neg
    apply congrArg (fun (h : Arity.arity LogicalSymbol.neg > 0) =>
      AdmissibleWord.app LogicalSymbol.neg h (fun _ => Q))
    exact proof_irrel H (by decide)
  · intro Q' hQ'
    unfold neg at hQ'
    have hf := app_args_inj LogicalSymbol.neg hQ'
    apply huniq
    simpa using hf

-- A unary (arity-1) node is uniquely `neg` of its unique argument.
theorem binary_unique (c : LogicalSymbol) (hc : Arity.arity c = 2) (ha : Arity.arity c > 0)
    (hq : Arity.arity c > 0)
    (f : Fin (Arity.arity c) → Proposition) :
    ∃! (p : Proposition × Proposition),
      AdmissibleWord.app c ha f =
        AdmissibleWord.app c hq (fun i : Fin (Arity.arity c) => if i.val = 0 then p.1 else p.2) := by
  let q1 : Proposition := f ⟨0, by simp [hc]⟩
  let q2 : Proposition := f ⟨1, by simp [hc]⟩
  refine ⟨(q1, q2), ?_, ?_⟩
  · have hf : f = (fun i : Fin (Arity.arity c) => if i.val = 0 then q1 else q2) :=
      (arg2_cond c hc f q1 q2).mpr (by simp [q1, q2])
    rw [hf, proof_irrel ha hq]
  · intro pw hpw
    rcases pw with ⟨R1, R2⟩
    have harg := app_args_inj c hpw
    rcases (arg2_cond c hc f R1 R2).1 harg with ⟨h0, h1⟩
    exact Prod.ext (by simpa [q1] using h0.symm) (by simpa [q2] using h1.symm)

-- A binary node (head `c` of arity 2) is uniquely conj/disj of its two co-ordinates.
-- ----------------------------------------------------------------------------
-- Size and shape of a proposition

-- ----------------------------------------------------------------------------
theorem size_one_iff_atom (P : Proposition) :
    size P = 1 ↔ (∃ n, P = var n) ∨ P = top ∨ P = bot := by
  constructor
  · intro h
    cases P with
    | atom a ha =>
      cases a with
      | var n => left; use n; rfl
      | top   => right; left; rfl
      | bot   => right; right; rfl
      | neg   => contradiction
      | conj  => contradiction
      | disj  => contradiction
    | app a ha args =>
      have hbig : 1 < size (AdmissibleWord.app a ha args) :=
        lt_of_le_of_lt (size_pos (args ⟨0, ha⟩)) (size_arg_lt a ha args ⟨0, ha⟩)
      omega
  · intro h
    rcases h with (⟨n, rfl⟩ | rfl | rfl)
    · simp [size, var]
    · simp [size, top]
    · simp [size, bot]

-- size 1 ⇔ an atom (var/top/bot)
theorem size_gt_one_connective (P : Proposition) (h : size P > 1) :
    (∃! Q, P = neg Q) ∨
    (∃! p : Proposition × Proposition, P = conj p.1 p.2) ∨
    (∃! p : Proposition × Proposition, P = disj p.1 p.2) := by
  cases P with
  | atom _ _ => simp [size] at h
  | app a ha args =>
    cases a with
    | var n => contradiction
    | top   => contradiction
    | bot   => contradiction
    | neg =>
      left
      exact unary_unique ha args
    | conj =>
      right; left
      unfold conj
      exact binary_unique LogicalSymbol.conj rfl ha (by decide) args
    | disj =>
      right; right
      unfold disj
      exact binary_unique LogicalSymbol.disj rfl ha (by decide) args

end PropositionalLogic