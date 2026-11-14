module

public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

@[expose] public section
/-! A family of walks specified only on one interval can be extended outside
it by harmless one-edge walks in the complete graph. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem complete_graph_extend_interval_walks
    {V:Type*} (v:ℕ→V) (start n:ℕ)
    (hne:∀i,v i≠v (i+1))
    (q:∀i,start≤i→i<start+n→(SimpleGraph.completeGraph V).Walk (v i) (v (i+1))):
    ∃p:∀i,(SimpleGraph.completeGraph V).Walk (v i) (v (i+1)),
      ∀i (hi:start≤i) (hj:i<start+n),p i=q i hi hj:=by
  classical
  let p (i:ℕ):(SimpleGraph.completeGraph V).Walk (v i) (v (i+1)):=
    if h:start≤i ∧ i<start+n then q i h.1 h.2
    else .cons (by simpa only [SimpleGraph.completeGraph_eq_top,SimpleGraph.top_adj] using hne i) .nil
  refine ⟨p,?_⟩
  intro i hi hj
  dsimp only [p]
  split_ifs with h
  · rfl
  · exact False.elim (h ⟨hi,hj⟩)
end Oberwolfach
