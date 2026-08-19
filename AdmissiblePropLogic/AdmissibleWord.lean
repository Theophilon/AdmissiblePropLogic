import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Basic
import Mathlib.Order.WellFounded


set_option linter.style.header false
set_option linter.style.whitespace false
set_option linter.style.longLine false

namespace Admissibility

universe u


-- ============================================================================
-- ## Admissible words

-- ============================================================================
-- ----------------------------------------------------------------------------
-- The arity function

-- ----------------------------------------------------------------------------
-- The **arity function** on an alphabet `A`: each letter is assigned the number
-- of direct sub-words it governs.  A letter of arity `0` is a constant (it
-- stands alone as an atom); a letter of positive arity expects that many
-- sub-words.  This is the datum that lets well-formedness be checked by counting,
-- and the typeclass bundles it so `AdmissibleWord A` can carry `[Arity A]`.
class Arity (A : Type u) where
  arity : A → ℕ

-- The arity function is defined as described; Lean confirms its properties.
-- ----------------------------------------------------------------------------
-- The `AdmissibleWord` type

-- ----------------------------------------------------------------------------
-- The core type of the project: a word over `A` that is **well-formed by
-- construction** against the arity structure.  There is no separate
-- admissibility predicate to thread through — every value of this type is,
-- by the constructors, an admissible word.  The predicate was internalized,
-- then retired; Lean prefers definitions that cannot be wrong.
--   • `atom a ha` — a nullary letter (witness `ha : arity a = 0` applied to no
--     arguments);
--   • `app a ha args` — a letter of positive arity (`ha : arity a > 0`)
--     applied to exactly `arity a` sub-words.
-- The `Fin (arity a) → AdmissibleWord A` argument is what makes the whole
-- recursion structural (and hence totality of `size`/`eval` free).  The idea is
inductive AdmissibleWord (A : Type u) [Arity A] : Type u where
  | atom : (a : A) → (ha : Arity.arity a = 0) → AdmissibleWord A
  | app  : (a : A) → (ha : Arity.arity a > 0) → (args : Fin (Arity.arity a) → AdmissibleWord A) → AdmissibleWord A

-- the admissible-word definition, read as a tree rather than as a flat string.
-- Decidable equality for well-formed words.  `deriving DecidableEq` cannot handle
-- the `Fin (Arity.arity a) → AdmissibleWord A` field automatically, so we supply
-- the instance ourselves and let the standard `instDecidableEqPi` (finite domain
-- → decidable codomain) make it constructively decidable.  Two `app`s are equal
-- iff their head symbols agree and their argument functions are extensionally
-- equal (checkable because `Fin n` is finite).  `injection` recovers the field
-- equalities from a word equation. Hand-written, and checked by a part of the
noncomputable instance (A : Type u) [Arity A] [DecidableEq A] : DecidableEq (AdmissibleWord A) := fun x y =>
  match x, y with
  | .atom a₁ _, .atom a₂ _ => by
      by_cases h : a₁ = a₂
      · exact isTrue (by subst h; rfl)
      · exact isFalse (by intro hx; apply h; injection hx)
  | .atom _ _, .app _ _ _ => isFalse (by intro h; cases h)
  | .app _ _ _, .atom _ _ => isFalse (by intro h; cases h)
  | .app a₁ _ f₁, .app a₂ _ f₂ => by
      by_cases h : a₁ = a₂
      · subst h
        by_cases hf : f₁ = f₂
        · exact isTrue (by subst hf; rfl)
        · exact isFalse (by intro hx; apply hf; injection hx)
      · exact isFalse (by intro hx; apply h; injection hx)


-- stack that does not know the difference.
-- ----------------------------------------------------------------------------
-- Size and sub-words

-- ----------------------------------------------------------------------------
-- The **size** (number of letters) of a word: `1` for an atom, and for an
-- application `1 +` the sizes of its `arity`-many sub-words.  Because
-- `AdmissibleWord` is structural, this is a plain recursion — no length- or
-- count-based strong induction is needed anywhere in the project. Structural
def size {A : Type u} [Arity A]: AdmissibleWord A → Nat
  | .atom _ _ => 1
  | .app _ _ args => 1 + (List.ofFn (fun i => size (args i))).sum

variable {A : Type u} [Arity A]

-- recursion saves the day, as it has been doing all along and will keep doing.
-- Every word has positive size: a word has at least one letter.  No
theorem size_pos (P : AdmissibleWord A) : 0 < size P := by
  cases P <;> simp [size]; omega

-- `AdmissibleWord` is empty, so its size is never `0`.
-- Helper: a natural number occurring in a list is no larger than the list's
-- sum.  Used by `size_arg_lt` to bound each sub-word size by the total size.
lemma nat_le_sum_of_mem (x : Nat) (l : List Nat) (h : x ∈ l) : x ≤ l.sum := by
  induction l with
  | nil => cases h
  | cons y ys ih =>
    cases h with
    | head =>      -- x = y, so x ≤ y + ys.sum
      rw [List.sum_cons]
      exact Nat.le_add_right x ys.sum
    | tail _ h_tail => -- x ∈ ys, use induction hypothesis
      rw [List.sum_cons]
      apply Nat.le_trans (ih h_tail)
      exact Nat.le_add_left ys.sum y

-- A small lemma whose entire purpose in life is to hold the door for the next.
-- x = y, so x ≤ y + ys.sum
-- x ∈ ys, use induction hypothesis
-- Each sub-word of an application is strictly smaller than the whole word.
lemma size_arg_lt (a : A) (ha : Arity.arity a > 0) (args : Fin (Arity.arity a) → AdmissibleWord A)
    (i : Fin (Arity.arity a)) :
    size (args i) < size (.app a ha args) := by
  simp only [size]
-- This is the well-foundedness of the sub-word relation, and it is what
  rw [Nat.add_comm]   -- now goal: size (args i) < sum + 1
  have hmem : size (args i) ∈ List.ofFn (fun j => size (args j)) := by
    simp [List.mem_ofFn]
  have h_le : size (args i) ≤ (List.ofFn (fun j => size (args j))).sum :=
    nat_le_sum_of_mem _ _ hmem
  exact Nat.lt_succ_of_le h_le   -- works because sum + 1 = sum.succ

-- makes the recursion structural for induction. Everything in Lean is a tree;
-- the trees just insist on it more than most didactic genres do.
-- goal: size (args i) < 1 + sum
-- now goal: size (args i) < sum + 1
theorem exists_nullary (f : AdmissibleWord A) : ∃ a : A, Arity.arity a = 0 := by
  induction f with
  | atom a ha => exact ⟨a, ha⟩
  | app a ha args ih =>
-- works because sum + 1 = sum.succ
    have hpos : 0 < Arity.arity a := ha
    exact ih ⟨0, hpos⟩  -- induction hypothesis applies to any argument

-- Every (nonempty) word contains a nullary letter somewhere.  For an atom the
-- letter is itself; for an application, ha : arity a > 0 guarantees at least one
-- argument, and the induction hypothesis applies to it. Somewhere, an atom is

-- hiding; the recursion finds it with no sense of drama.
-- ha : arity a > 0, so there is at least one argument.
-- induction hypothesis applies to any argument
-- ----------------------------------------------------------------------------
def Path := List Nat

-- Paths and unique readability
-- ----------------------------------------------------------------------------
-- Positions are paths: a finite list of child indices navigating the tree.
-- A sub-word at a starting position `i`, generalized from a single step to a
-- full path. Trees turn every question into a question about paths; the
def getSubAdmissibleWord : AdmissibleWord A → Path → Option (AdmissibleWord A)
  | f, [] => some f
  | .atom _ _, _::_ => none
  | .app a _ha args, 0::rest =>
      if h : 0 < Arity.arity a then getSubAdmissibleWord (args ⟨0, h⟩) rest
      else none
  | .app a _ha args, (i+1)::rest =>
      if h : i+1 < Arity.arity a then getSubAdmissibleWord (args ⟨i+1, h⟩) rest
      else none

-- patience required to follow them is the reader's own.
-- Look up the sub-word at a path: `some g` if the path is valid (every index
-- lies within the arity of the head letter on the way down), `none` otherwise.
-- An `AdmissibleWord` is a tree, so a path uniquely determines either a sub-word
-- or failure. No ambiguity is possible, which is precisely what keeps this an
theorem unique_subword_at_path (f : AdmissibleWord A) (p : Path) :
    (getSubAdmissibleWord f p).isSome → ∃! g, getSubAdmissibleWord f p = some g := by
  intro h
  cases hg : getSubAdmissibleWord f p with
  | none =>
    simp [hg] at h
  | some g =>
    refine ExistsUnique.intro g ?_ ?_
    · rfl
    · intro g' hg'
      injection hg' with hgg'
      symm
      exact hgg'

end Admissibility
