module

public import Oberwolfach.CommonNeighborhoodSubgraphPhysical

@[expose] public section
/-! A finite forbidden rim-edge set has bounded deletion degree at every
vertex; no randomness or density factor is used for this loss. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finite_forbidden_rim_deletion_degree {V:Type} [Fintype V] [DecidableEq V]
    (G F₀:SimpleGraph V) (f:ℕ) (hf:F₀.edgeFinset.card≤f):
    ∀ v,((G\(G\F₀)).degree v:ℝ)≤f:=by
  intro v
  have hsub:G\(G\F₀)≤F₀:=by
    intro x y h
    exact Classical.byContradiction (fun hnot=>h.2 ⟨h.1,hnot⟩)
  have hh:((G\(G\F₀)).degree v:ℝ)≤F₀.degree v:=by
    exact_mod_cast SimpleGraph.degree_le_of_le hsub (v:=v)
  have ht:(F₀.degree v:ℝ)≤F₀.edgeFinset.card:=by
    exact_mod_cast F₀.degree_le_card_edgeFinset (v:=v)
  have hf':(F₀.edgeFinset.card:ℝ)≤f:=by exact_mod_cast hf
  linarith
theorem finite_forbidden_rim_deletion_degree_of_eq {V:Type} [Fintype V] [DecidableEq V]
    (G Q F₀:SimpleGraph V) (heq:Q=G\F₀) (f:ℕ) (hf:F₀.edgeFinset.card≤f):
    ∀ v,((G\Q).degree v:ℝ)≤f:=by
  intro v
  have hsub:G\Q≤F₀:=by
    intro x y h
    have he:Q.Adj x y↔G.Adj x y∧¬F₀.Adj x y:=by rw [heq];rfl
    exact Classical.byContradiction (fun hnot=>h.2 (he.mpr ⟨h.1,hnot⟩))
  have hh:((G\Q).degree v:ℝ)≤F₀.degree v:=by
    exact_mod_cast SimpleGraph.degree_le_of_le hsub (v:=v)
  have ht:(F₀.degree v:ℝ)≤F₀.edgeFinset.card:=by
    exact_mod_cast F₀.degree_le_card_edgeFinset (v:=v)
  have hf':(F₀.edgeFinset.card:ℝ)≤f:=by exact_mod_cast hf
  linarith

theorem cycle_in_forbidden_rim_complement {V:Type} [Fintype V] [DecidableEq V]
    (G F₀:SimpleGraph V) (r:ℕ) (C:OrdinaryCycle (G\F₀) r):
    Disjoint C.val.val.edgeFinset F₀.edgeFinset:=by
  apply Finset.disjoint_left.mpr
  intro e heC heF
  induction e using Sym2.ind with
  | _ v w =>
    have hc:C.val.val.Adj v w:=by simpa using heC
    have hf:F₀.Adj v w:=by simpa using heF
    exact (C.property hc).2 hf
end Oberwolfach
