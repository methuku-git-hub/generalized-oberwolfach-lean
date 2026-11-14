module

public import Oberwolfach.ClassRequiredGraphContainment
public import Oberwolfach.ColourReorientation

@[expose] public section
/-! Transfer degree and total-edge bounds from the sampled required graph to
the actual class graph, paying only for regularisation insertions. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem graph_le_sup_degree_and_edges
    {V:Type} [Fintype V] [DecidableEq V] (G A B:SimpleGraph V) (h:G≤A⊔B):
    (∀v,G.degree v≤A.degree v+B.degree v) ∧
      G.edgeFinset.card≤A.edgeFinset.card+B.edgeFinset.card:=by
  constructor
  · intro v
    have hn:G.neighborFinset v⊆(A⊔B).neighborFinset v:=by
      intro w hw
      exact (SimpleGraph.mem_neighborFinset _ _ _).mpr (h ((SimpleGraph.mem_neighborFinset _ _ _).mp hw))
    exact (Finset.card_le_card hn).trans (graph_sup_degree_le A B v)
  · have he:(A⊔B).edgeFinset=A.edgeFinset∪B.edgeFinset:=by
      ext e
      simp only [Finset.mem_union,SimpleGraph.mem_edgeFinset,SimpleGraph.edgeSet_sup,Set.mem_union]
    have hm:=Finset.card_le_card (SimpleGraph.edgeFinset_mono h)
    rw [he] at hm
    exact hm.trans (Finset.card_union_le _ _)

theorem class_required_graph_edit_bounds
    {V:Type} [Fintype V] [LinearOrder V]
    (P S₀ S Used Sel:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (I:Finset V) (D:V→V→Prop)
    (hSP:S≤P):
    let K:=longRequiredPhysicalGraph S (S\Used) Sel π d I D (fun x y=>Used.Adj x y)
    let K₀:=longRequiredPhysicalGraph P (S₀\Used) Sel π d I D (fun x y=>Used.Adj x y)
    let E:=spanningRestriction (S\S₀) I
    (∀v,K.degree v≤K₀.degree v+E.degree v) ∧
      K.edgeFinset.card≤K₀.edgeFinset.card+E.edgeFinset.card:=by
  intro K K₀ E
  exact graph_le_sup_degree_and_edges K K₀ E
    (class_required_graph_le_sampled_with_insertions P S₀ S Used Sel π d I D hSP)
end Oberwolfach
