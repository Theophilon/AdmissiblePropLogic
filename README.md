# AdmissiblePropLogic — `compact` branch

*An AI-generated formalization of propositional logic. The proofs are real. The ambition is synthetic — and, on this branch, compact.*

![Lean 4.34.0-rc1](https://img.shields.io/badge/Lean-4.34.0--rc1-blue)
![mathlib v4.34.0-rc1](https://img.shields.io/badge/mathlib-v4.34.0--rc1-blue)
![License: MIT](https://img.shields.io/badge/License-MIT-green)
![written by: a machine](https://img.shields.io/badge/written%20by-a%20machine-blueviolet)

## What this branch is

This is what happens when you ask a language model to formalize propositional
logic, it says yes, and then a proof assistant — which has no sense of humor
and no tolerance for `sorry` — agrees to check every single step. Then you ask
both of them to **use only two connectives and drag in as little mathlib as
possible**, and the machine, which was not consulted about its feelings, agrees
to that too.

Every theorem here is machine-checked by Lean. Every word here was also written
by a machine. We would like you to be able to tell which of those two facts is
the more reassuring one, but the README is not equipped to make that judgment.

## Highlights

- **Only implication and negation.** The alphabet keeps exactly two primitive
  connectives — `neg` (`¬`) and `impl` (`→`). Everything else is *derived*:
  `top := impl P₀ P₀`, `bot := neg top`, `conj P Q := neg (impl P (neg Q))`,
  and `disj P Q := impl (neg P) Q`. A malformed formula cannot even be
  expressed; a connective that could be defined instead cannot be axiomatized.
- **A minimal Hilbert basis.** The provability relation `Ded` is a
  six-constructor classical system — `assm`, `imp_1`, `imp_2`, `neg_contra`,
  `raa`, `mp`. The former connectives' axioms (`top_intro`, `conj_*`,
  `disj_*`, `neg_elim`, `efq`) are *theorems*, not axioms. Even `neg_elim`,
  `contrapos`, and `conj_intro` are derived on the primitive base.
- **Compact.** On this branch the dependency graph is smaller: the whole
  project builds in ~970 jobs rather than ~3000, and `NormalForms` — the one
  file that had been importing the entire `Mathlib.Tactic` umbrella — cold-builds
  in about seven seconds instead of double digits.
- **0 errors / 0 warnings / 0 `sorry`.** This is the one fact the project
  would like you to know very much.
- **CI runs on every push**, so any future regression is immediately and
  publicly documented. The AI is not nervous. The AI is the one committing.

## The core type

```lean
class Arity (A : Type u) where
  arity : A → ℕ

inductive AdmissibleWord (A : Type u) [Arity A] : Type u where
  | atom : (a : A) → (ha : Arity.arity a = 0) → AdmissibleWord A
  | app  : (a : A) → (ha : Arity.arity a > 0)
           → (args : Fin (Arity.arity a) → AdmissibleWord A) → AdmissibleWord A
```

A proposition is an admissible word over the logical symbols:

```lean
inductive LogicalSymbol
  | var : Nat → LogicalSymbol | neg | impl

abbrev Proposition := AdmissibleWord LogicalSymbol
```

The alphabet keeps only the two *primitive* connectives, `neg` and `impl`
(implication). Everything else is derived on top of them: `top := impl P₀ P₀`,
`bot := neg top`, `conj P Q := neg (impl P (neg Q))`, and `disj P Q :=
impl (neg P) Q`. Because each connective's arity is built into the alphabet,
`Proposition` is the well-formed-formula type. Malformed formulas do not exist
here, in the same way that bugs do not exist in software that was never run.

## What is proved

The statements are Lean's own. The commentary is the AI's.

| Area | Result |
|---|---|
| **Size** | unique readability: size 1 ⇔ an atom; size > 1 ⇔ one connective |
| **Semantics** | `eval` depends only on the variables used; `Equivalent` is an equivalence relation; the twelve laws of propositional equivalence |
| **Proof system** | Hilbert `Ded` over `{¬, →}`, the Deduction Lemma, monotonicity, compactness of the derivation relation |
| **Soundness** | `T ⊢ P ⇒ T ⊨ P`; satisfiable theories are consistent |
| **Completeness** | Henkin style: consistent ⇒ satisfiable; `T ⊨ P ⇒ T ⊢ P` |
| **Compactness** | `T ⊨ P ⇒ ∃` finite `T₀ ⊆ T, T₀ ⊨ P` |
| **Application** | `compactness_bipartite`: every finitely-bipartite graph is bipartite. A compactness theorem went into graph theory and it won. |
| **Normal forms** | `dnf_normal_form` / `cnf_normal_form`: everything has a normal form |

## Project layout

The modules are listed in dependency order.

| Module | Contents |
|---|---|
| `AdmissibleWord` | `Arity` + the core type; `size`, paths / sub-word lookup |
| `Proposition` | `LogicalSymbol`, `Proposition`, the 3 primitive + 4 derived connectives, size ⇔ shape |
| `Semantics` | truth assignments, `eval`, tautology / equivalence / entailment |
| `ProofSystem` | the minimal `Ded`, derived rules, the Deduction Lemma |
| `Soundness` | provability ⇒ entailment; satisfiable ⇒ consistent |
| `Completeness` | Henkin model existence: consistent ⇒ satisfiable |
| `Compactness` | compactness + the bipartite-graph two-coloring application |
| `NormalForms` | `InDNF`/`InCNF`, `dnfOf`/`cnfOf`, existence + equivalence |

## Getting started

You will need **Lean**, **elan**, and a willingness to let mathlib download
itself onto your machine. The first `lake build` downloads a considerable
fraction of the internet on your behalf. This is normal.

```bash
lake build
```

On the pinned toolchain, this builds at **0 errors / 0 warnings**, in about
nine seconds from a cold start, across roughly 970 modules (down from three
thousand). Which we are currently prepared to state in writing.

```lean
#check soundness
#check dnf_normal_form
#check compactness_bipartite
```

## The compact philosophy

Two reductions, in order of ambition:

1. **The logical one** — the alphabet is `{var, neg, impl}` and `Ded` is the
   six-constructor classical base. Every other connective and every other
   axiom scheme is a derived theorem. This is what the title of the old branch
   (`experiment-impl-not`) was gesturing at; the branch is now called
   `compact` because it got the point.
2. **The computational one** — a single over-broad import in `NormalForms`
   (`Mathlib.Tactic`, the whole folder) was pulling roughly two thousand
   modules into the build graph. Narrowing it to `Mathlib.Tactic.Basic` +
   `Mathlib.Tactic.Linarith` + `Mathlib.Data.Fintype.Pi` cut the graph to
   about a third. The proofs were too busy to notice; `simp` and `omega`
   still do their jobs.

## Acknowledgements

This project is AI-generated in the most literal sense: the proofs were drafted
by [Hermes Agent](https://hermes-agent.nousresearch.com) (Nous Research),
running a DeepSeek model (`deepseek-v4-flash-0731`) via OpenRouter, and then
verified by Lean. So the ground truth here is not merely "an AI wrote it" — it
is that a proof assistant stamped every claim. The AI is nonetheless entirely
responsible for the phrasing, and it accepts that responsibility with the
serenity of something that does not experience embarrassment.

The provability relation `T ⊢ P` is the inductive family `Ded`: a derivation
**is** an inhabitant, each axiom scheme is a constructor, and Modus Ponens is
the single rule. The family is built over just the two primitive connectives
and its six constructors — `assm`, `imp_1`, `imp_2`, `neg_contra`, `raa`, `mp`
— so the whole classical theory of `{¬, →}` is recovered without a single
connective being axiomatized that could be derived instead.

The inductive-family encoding of `Ded` is modeled on
[`guodk/PropLogicLean`](https://github.com/guodk/PropLogicLean) — *Formalizing
the Completeness Theorem for Propositional Logic in Lean 4* — and the encoding
style also follows [`m4lvin/lean4-pdl`](https://github.com/m4lvin/lean4-pdl).
Our reduction to the primitive `{¬, →}` alphabet is this project's own; the
proof skeleton `Ded` uses is theirs.

The development follows an undergraduate lecture note on mathematical logic.
The course, institution, and author are not named, because some information is
meant to stay private, and the AI respects that more than it respects the
reader's desire for citations.

## License

MIT.