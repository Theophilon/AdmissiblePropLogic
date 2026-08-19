import Mathlib.Data.Countable.Defs
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Set.Finite.Range
import AdmissiblePropLogic.Soundness
import AdmissiblePropLogic.Completeness

set_option linter.style.header false
set_option linter.style.whitespace false
set_option linter.style.longLine false

namespace PropositionalLogic

open Admissibility

-- ============================================================================
-- ## Compactness
-- ============================================================================

-- The graph vertex type is allowed to live in any universe `u`; it is completely
-- independent of the base universe of `Proposition` (a design point, so the graph
-- application does not force the vertex type down into `Type`).
-- A small liberty with universes; permitted, because nothing unsound follows from it.
universe u

-- Compactness for entailment
-- For any proposition P, if T ⊨ P, then there exists a finite subset
-- T₀ of T such that T₀ ⊨ P.
-- Consumes the chain: Completeness (entailment implies provability, `entailment_implies_deductible`)
-- gives `T ⊢ P`; the `finite_subproof` lemma extracts a finite `T₀ ⊆ T` that
-- already proves `P`; Soundness turns that back into `Entails T₀ P`.
-- Whatever is true was already true on some finite witness; logic is careful
-- with its receipts.
theorem compactness_entails {T : Set Proposition} {P : Proposition} (h : Entails T P) :
    ∃ T₀ : Set Proposition, T₀.Finite ∧ T₀ ⊆ T ∧ Entails T₀ P := by
  have hded : T ⊢ P := entailment_implies_deductible h
  rcases finite_subproof hded with ⟨T₀, hfin, hsub, hded₀⟩
  exact ⟨T₀, hfin, hsub, soundness hded₀⟩

-- Compactness for consistency
-- If every finite subset of T is consistent, then T is consistent.
-- This is the classical contrapositive of `consistent_of_finite_consistent`: were `T` inconsistent,
-- that lemma would hand us a *finite* inconsistent `T₀ ⊆ T`, contradicting the hypothesis.
-- The contrapositive carries the argument; Lean raises no philosophical objection.
theorem compactness_consistent {T : Set Proposition}
    (h : ∀ T₀ : Set Proposition, T₀.Finite → T₀ ⊆ T → Consistent T₀) : Consistent T := by
  classical
  unfold Consistent
  intro hincon
  rcases consistent_of_finite_consistent hincon with ⟨T₀, hfin, hsub, hincon₀⟩
  exact h T₀ hfin hsub hincon₀

-- ----------------------------------------------------------------------------
-- Application: compactness and bipartite graphs
-- ----------------------------------------------------------------------------
--
-- The graph here is "simple and symmetric" (irreflexive symmetric `Adj`),
-- which is exactly Mathlib's `SimpleGraph V`.  We reuse it rather than hand-roll
-- a new structure (matching the project philosophy of never re-defining Mathlib).
-- Re-implementing a well-typed standard structure is a hobby we declined.

-- Definition — Bipartite graph
-- G is bipartite if there are nonempty V₀, V₁ ⊆ V covering V,
-- disjoint, with no edge internal to either part.
-- Kept in the *partition* form as the primitive notion.
def Bipartite {V : Type u} (G : SimpleGraph V) : Prop :=
  ∃ V₀ V₁ : Set V,
    V₀.Nonempty ∧ V₁.Nonempty ∧
    (∀ v, v ∈ V₀ ∨ v ∈ V₁) ∧
    V₀ ∩ V₁ = ∅ ∧
    (∀ ⦃v w⦄, v ∈ V₀ → w ∈ V₀ → ¬ G.Adj v w) ∧
    (∀ ⦃v w⦄, v ∈ V₁ → w ∈ V₁ → ¬ G.Adj v w)

-- The right-hand side of the two-coloring lemma: a *surjective* two-coloring `f : V → {0,1}`
-- such that adjacent vertices get different colors.  The surjectivity is retained
-- to match a `f : V → {0, 1}`-valued coloring faithfully.
-- This matters in the finitely-bipartite theorem: a non-empty graph's compactness-built coloring is
-- automatically surjective, but an *edgeless* graph is handled separately there
-- (a constant coloring would not be surjective).
def HasTwoColoring {V : Type u} (G : SimpleGraph V) : Prop :=
  ∃ f : V → Bool, Function.Surjective f ∧ ∀ ⦃v w⦄, G.Adj v w → f v ≠ f w

-- Bipartite iff two-coloring
-- G is bipartite iff it admits a surjective two-coloring.
-- (→) From the partition: color `v` false in `V₀`, true outside (surjectivity
-- comes from `V₀`, `V₁` both nonempty; the no-monochrome-edge condition follows
-- from the two "no internal edge" hypotheses).
-- (←) From a coloring: `V₀ := {v | f v = false}`, `V₁ := {v | f v = true}`;
-- surjectivity makes both nonempty, `Bool` decidability gives the cover, and
-- distinct colors on edges give "no internal edge".
-- A graph is exactly as far from bipartite as its nearest coloring; Lean agrees.
theorem bipartite_iff_two_coloring {V : Type u} (G : SimpleGraph V) :
    Bipartite G ↔ HasTwoColoring G := by
  classical
  constructor
  · -- partition → coloring
    rintro ⟨V₀, V₁, h0non, h1non, hcover, hdisj, h00, h11⟩
    let f : V → Bool := fun v => if v ∈ V₀ then false else true
    refine ⟨f, ?_, ?_⟩
    · -- The coloring `f` is surjective.
      intro b
      cases b
      · -- Some vertex of `V₀` is colored false.
        rcases h0non with ⟨v0, hv0⟩
        exact ⟨v0, by simp [f, hv0]⟩
      · -- Some vertex of `V₁` (which avoids `V₀` by disjointness) is colored true.
        rcases h1non with ⟨v1, hv1⟩
        have hv1not : v1 ∉ V₀ := by
          intro hv1₀
          have : v1 ∈ (V₀ ∩ V₁ : Set V) := ⟨hv1₀, hv1⟩
          rw [hdisj] at this
          exact this
        exact ⟨v1, by simp [f, hv1not]⟩
    · -- No edge is monochromatic.
      intro v w hE
      by_cases hv : v ∈ V₀
      · have hw : w ∉ V₀ := by
          intro hw₀
          exact h00 hv hw₀ hE
        have hfv : f v = false := by simp [f, hv]
        have hfw : f w = true := by simp [f, hw]
        rw [hfv, hfw]
        simp
      · -- v ∉ V₀; if w were not in V₀ either, both would lie in V₁, giving an
        -- internal edge — contradiction.  So w ∈ V₀ and the colors differ.
        have hw' : w ∈ V₀ := by
          by_contra hwnot
          have hv1 : v ∈ V₁ := (hcover v).resolve_left hv
          have hw1 : w ∈ V₁ := (hcover w).resolve_left hwnot
          exact h11 hv1 hw1 hE
        have hfv : f v = true := by simp [f, hv]
        have hfw : f w = false := by simp [f, hw']
        rw [hfv, hfw]
        simp
  · -- coloring → partition
    rintro ⟨f, hsurj, hcol⟩
    let V₀ : Set V := {v | f v = false}
    let V₁ : Set V := {v | f v = true}
    refine ⟨V₀, V₁, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- `V₀` is nonempty (surjectivity at false).
      rcases hsurj false with ⟨v, hv⟩
      exact ⟨v, hv⟩
    · -- `V₁` is nonempty (surjectivity at true).
      rcases hsurj true with ⟨v, hv⟩
      exact ⟨v, hv⟩
    · -- The cover is trivial: `Bool` is two-valued.
      intro v
      cases h : f v
      · left; exact h
      · right; exact h
    · -- The two parts are disjoint.
      ext v
      simp [V₀, V₁]
    · -- There are no internal edges in `V₀`.
      intro v w hv hw hE
      exact (hcol hE) (by rw [hv, hw])
    · -- There are no internal edges in `V₁`.
      intro v w hv hw hE
      exact (hcol hE) (by rw [hv, hw])

-- ----------------------------------------------------------------------------
-- Compactness shows every "finitely bipartite" graph is bipartite
-- ----------------------------------------------------------------------------
--
-- The edge gadget: an edge `{v, w}` becomes the XOR proposition
--   (P_v and not P_w) or (not P_v and P_w),
-- which is satisfied exactly when the assignment gives `v` and `w` different colors.
-- (`edgeProposition` is built directly from the intrinsic `var`/`conj`/`disj`/`neg` constructors.)
-- An edge, encoded as a small disagreement: the two colors may not be the same.
def edgeProposition {V : Type u} (enc : V → ℕ) (v w : V) : Proposition :=
  disj (conj (var (enc v)) (neg (var (enc w))))
       (conj (neg (var (enc v))) (var (enc w)))

-- The edge gadget evaluates to `true` exactly when the two encoded vertices get
-- different truth values (a truth-functional XOR identity on the two Bool values).
theorem eval_edgeProposition {V : Type u} {t : TruthAssignment} {enc : V → ℕ} {v w : V} :
    eval t (edgeProposition enc v w) = true ↔ t (enc v) ≠ t (enc w) := by
  simp [edgeProposition, eval_disj, eval_conj, eval_neg, eval_var]
  cases t (enc v) <;> cases t (enc w) <;> simp

-- The theory encoding all edges of `G` under the vertex encoding `enc`:
--   Q in Th  iff  Q is the edge gadget for some actual edge of G.
-- (Written directly over the intrinsic `Proposition` type.)
def graphTheory {V : Type u} (G : SimpleGraph V) (enc : V → ℕ) : Set Proposition :=
  { Q | ∃ p : V × V, G.Adj p.1 p.2 ∧ Q = edgeProposition enc p.1 p.2 }

-- Every *finite* subset `T₀` of the edge theory is satisfiable: collect the finitely
-- many vertices appearing in `T₀`'s edge gadgets into a finite `V₀`, apply the
-- finite-subgraph hypothesis to get a two-coloring `f` of the induced graph on `V₀`,
-- then extend `f` to a global assignment (false off `V₀`).
--   • an *empty* `T₀` is trivially satisfiable;
--   • a *nonempty* `T₀` yields some edge, so `V₀` has at least two vertices and the
--     `V₀.Nontrivial` hypothesis applies.
-- Finiteness is what makes the guess honest; beyond it, compactness takes over.
lemma finite_subgraph_satisfiable {V : Type u}
    (G : SimpleGraph V)
    (hfinite : ∀ V₀ : Set V, V₀.Finite → V₀.Nontrivial → Bipartite (SimpleGraph.induce V₀ G))
    (enc : V → ℕ) (henc : Function.Injective enc)
    {T₀ : Set Proposition} (hT0sub : T₀ ⊆ graphTheory G enc) (hT0Fin : T₀.Finite) :
    Satisfiable T₀ := by
  classical
  -- `haveI` registers `Finite T₀` so `Set.finite_range` below can use it as an instance.
  set_option linter.style.haveILetI false in
  by_cases hT0empty : T₀ = ∅
  · -- An empty finite subset is trivially satisfiable.
    rw [hT0empty]
    exact empty_satisfiable
  · -- A nonempty subset: build the finite vertex set `V₀` from `T₀`'s edges.
    rcases (Set.nonempty_iff_ne_empty.mpr hT0empty) with ⟨w0, hw0⟩
    let edgeOf : T₀ → V × V := fun x => Classical.choose (hT0sub x.2)
    have edgeOf_spec : ∀ x : T₀,
        G.Adj (edgeOf x).1 (edgeOf x).2 ∧ x.1 = edgeProposition enc (edgeOf x).1 (edgeOf x).2 :=
      fun x => Classical.choose_spec (hT0sub x.2)
    let V₀ : Set V := { v | ∃ x : T₀, v = (edgeOf x).1 ∨ v = (edgeOf x).2 }
    -- V₀ is finite: it is the union of the two finite index sets (T₀ is finite).
    have hV0Fin : V₀.Finite := by
      haveI : Finite T₀ := hT0Fin
      have h1 : Set.Finite (Set.range (fun x : T₀ => (edgeOf x).1)) :=
        Set.finite_range (fun x : T₀ => (edgeOf x).1)
      have h2 : Set.Finite (Set.range (fun x : T₀ => (edgeOf x).2)) :=
        Set.finite_range (fun x : T₀ => (edgeOf x).2)
      refine Set.Finite.subset (Set.Finite.union h1 h2) ?_
      intro v hv
      rcases hv with ⟨x, hx⟩
      rw [Set.mem_union]
      rcases hx with h | h
      · left; exact ⟨x, h.symm⟩
      · right; exact ⟨x, h.symm⟩
    -- V₀ has at least two vertices: the edge carried by the nonempty witness x₀
    -- contributes two distinct endpoints (a `SimpleGraph` edge is never a loop).
    have hV0Nontriv : V₀.Nontrivial := by
      let e : V × V := edgeOf ⟨w0, hw0⟩
      have hE : G.Adj e.1 e.2 := (edgeOf_spec ⟨w0, hw0⟩).1
      have hne : e.1 ≠ e.2 := hE.ne
      refine ⟨e.1, ?_, e.2, ?_, hne⟩
      · exact ⟨⟨w0, hw0⟩, Or.inl rfl⟩
      · exact ⟨⟨w0, hw0⟩, Or.inr rfl⟩
    -- The finite-subgraph hypothesis, with the two-coloring lemma, yields a two-coloring `f` of the induced graph.
    rcases hfinite V₀ hV0Fin hV0Nontriv with hBip
    rcases (bipartite_iff_two_coloring (SimpleGraph.induce V₀ G)).mp hBip with
      ⟨f, hsurj, hprop⟩
    -- Global assignment: encode a vertex as its color when it lies in `V₀`, else false.
    let t : TruthAssignment :=
      fun n => if h : ∃ v : V, v ∈ V₀ ∧ enc v = n then f ⟨Classical.choose h, (Classical.choose_spec h).1⟩ else false
    refine ⟨t, ?_⟩
    intro x hx
    let x₀ : T₀ := ⟨x, hx⟩
    let e : V × V := edgeOf x₀
    have hE : G.Adj e.1 e.2 := (edgeOf_spec x₀).1
    have hxEq : x = edgeProposition enc e.1 e.2 := (edgeOf_spec x₀).2
    have hmem1 : e.1 ∈ V₀ := ⟨x₀, Or.inl rfl⟩
    have hmem2 : e.2 ∈ V₀ := ⟨x₀, Or.inr rfl⟩
    -- The two encoded vertices pick up exactly their coloring (because `enc` is injective).
    have hte1 : t (enc e.1) = f ⟨e.1, hmem1⟩ := by
      dsimp [t]
      have hEx : ∃ v : V, v ∈ V₀ ∧ enc v = enc e.1 := ⟨e.1, hmem1, rfl⟩
      rw [dite_eq_left hEx]
      exact congrArg f (Subtype.ext (henc (Classical.choose_spec hEx).2))
    have hte2 : t (enc e.2) = f ⟨e.2, hmem2⟩ := by
      dsimp [t]
      have hEx : ∃ v : V, v ∈ V₀ ∧ enc v = enc e.2 := ⟨e.2, hmem2, rfl⟩
      rw [dite_eq_left hEx]
      exact congrArg f (Subtype.ext (henc (Classical.choose_spec hEx).2))
    -- The edge carries two different colors, hence its XOR gadget evaluates to true.
    have hprop' : f ⟨e.1, hmem1⟩ ≠ f ⟨e.2, hmem2⟩ := by
      have hAdj : (SimpleGraph.induce V₀ G).Adj ⟨e.1, hmem1⟩ ⟨e.2, hmem2⟩ := by
        exact hE
      exact hprop hAdj
    have hneq : t (enc e.1) ≠ t (enc e.2) := by
      rw [hte1, hte2]
      exact hprop'
    have hEdgeTrue : eval t (edgeProposition enc e.1 e.2) = true :=
      (eval_edgeProposition.mpr hneq)
    rw [hxEq]
    exact hEdgeTrue

-- Finitely-bipartite graphs are bipartite
-- Let G = (V, E) be a simple and symmetric graph.  Suppose V is countably infinite
-- (`[Countable V]` + `[Infinite V]`) and every finite subgraph with at least two
-- vertices is bipartite.  Then G is bipartite.
--
-- Sketch.  Split on whether `G` has an edge.
--   • Edgeless `G`: every finite graph is trivially "no internal edge", and
--     `[Infinite V]` supplies two distinct vertices, giving an immediate
--     bipartition.  (The compactness-built coloring would be constant here, so it is
--     NOT surjective — this is why the edgeless case is handled directly rather than
--     forced through `HasTwoColoring`.)
--   • `G` has an edge: the finite-satisfiable argument (`finite_subgraph_satisfiable`)
--     makes the edge theory finitely satisfiable, hence satisfiable by compactness
--     (`compactness_consistent` → `consistent_of_satisfiable` → `model_existence`).
--     The satisfying assignment colors every vertex via `t ∘ enc`; because `G` has at
--     least one edge, both colors are actually attained, so the coloring is surjective
--     and the two-coloring lemma turns it into a bipartition.
-- Local good behavior, carried up to infinity by compactness; a ride the machine has
-- agreed to certify, which is more than most elevators can claim.
theorem compactness_bipartite {V : Type u} [Countable V] [Infinite V]
    (G : SimpleGraph V)
    (hfinite : ∀ V₀ : Set V, V₀.Finite → V₀.Nontrivial → Bipartite (SimpleGraph.induce V₀ G)) :
    Bipartite G := by
  classical
  by_cases hedgeless : ∀ v w : V, ¬ G.Adj v w
  · -- Edgeless case: split V directly into two nonempty parts (both have no internal edges).
    rcases (by
      -- V is infinite, so it has two distinct vertices.
      by_contra hnot
      push Not at hnot
      have hsub : Subsingleton V := Subsingleton.intro (fun a b => hnot a b)
      have hfin : Finite V := @Finite.of_subsingleton V hsub
      exact (not_infinite_iff_finite.mpr hfin) (inferInstance : Infinite V)
      : ∃ a b : V, a ≠ b) with ⟨a, b, hab⟩
    let V₀ : Set V := {a}
    let V₁ : Set V := {v | v ≠ a}
    refine ⟨V₀, V₁, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact ⟨a, by simp [V₀]⟩
    · exact ⟨b, by simp [V₁, hab.symm]⟩
    · intro v
      by_cases hv : v = a
      · left; simp [V₀, hv]
      · right; simp [V₁, hv]
    · ext v
      simp [V₀, V₁]
    · intro v w hv hw hE
      exact hedgeless v w hE
    · intro v w hv hw hE
      exact hedgeless v w hE
  · -- Has-an-edge case: use compactness.
    rcases Countable.exists_injective_nat V with ⟨enc, henc⟩
    let Th : Set Proposition := graphTheory G enc
    -- Every finite subset of Th is satisfiable (the finite-subgraph argument).
    have hfin : ∀ T₀ : Set Proposition, T₀ ⊆ Th → T₀.Finite → Satisfiable T₀ := by
      intro T₀ hsub hfin
      exact finite_subgraph_satisfiable G hfinite enc henc hsub hfin
    -- Compactness makes Th consistent, then model existence supplies a satisfying assignment.
    have hcons : Consistent Th := compactness_consistent (by
      intro T₀ hfinT0 hsub
      exact consistent_of_satisfiable (hfin T₀ hsub hfinT0))
    rcases model_existence hcons with ⟨t, hSat⟩
    -- A real edge is present, to witness surjectivity of the coloring below.
    push Not at hedgeless
    rcases hedgeless with ⟨v0, w0, hE0⟩
    let f : V → Bool := fun v => t (enc v)
    refine (bipartite_iff_two_coloring G).mpr ⟨f, ?_, ?_⟩
    · -- Surjectivity: the edge forces both color values to occur.
      have hneq_edge : t (enc v0) ≠ t (enc w0) := by
        have hEdgeIn : edgeProposition enc v0 w0 ∈ Th := ⟨(v0, w0), hE0, rfl⟩
        have hEval : eval t (edgeProposition enc v0 w0) = true := hSat (edgeProposition enc v0 w0) hEdgeIn
        exact (eval_edgeProposition.mp hEval)
      intro b
      cases b
      · cases h : t (enc v0)
        · exact ⟨v0, by simpa [f] using h⟩
        · have hw : t (enc w0) = false := by
            cases h' : t (enc w0)
            · rfl
            · exfalso; simp [h, h'] at hneq_edge
          exact ⟨w0, by simpa [f] using hw⟩
      · cases h : t (enc v0)
        · have hw : t (enc w0) = true := by
            cases h' : t (enc w0)
            · exfalso; simp [h, h'] at hneq_edge
            · rfl
          exact ⟨w0, by simpa [f] using hw⟩
        · exact ⟨v0, by simpa [f] using h⟩
    · -- Distinct colors on every edge: the edge gadget is in Th and must be true.
      intro v w hE
      have hEdgeIn : edgeProposition enc v w ∈ Th := ⟨(v, w), hE, rfl⟩
      have hEval : eval t (edgeProposition enc v w) = true := hSat (edgeProposition enc v w) hEdgeIn
      have hneq : t (enc v) ≠ t (enc w) := (eval_edgeProposition.mp hEval)
      simpa [f] using hneq

end PropositionalLogic
