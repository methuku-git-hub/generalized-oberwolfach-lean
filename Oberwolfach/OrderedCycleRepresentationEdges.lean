module

public import Oberwolfach.OrderedCycleFirstEdgeInjective
public import Oberwolfach.OrderedCycleFirstEdgeExists

@[expose] public section
/-! Ordered representations of one fixed embedded cycle are in bijection
with its directed edges. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

abbrev OrderedCycleRepresentations {V:Type} (H:SimpleGraph V) (r:ℕ):=
  {f:Fin r↪V // H=(SimpleGraph.cycleGraph r).map f}

abbrev DirectedEdges {V:Type} (H:SimpleGraph V):={xy:V×V // H.Adj xy.1 xy.2}

def orderedCycleFirstEdge {V:Type} [Fintype V] [DecidableEq V] (H:SimpleGraph V) (n:ℕ)
    (f:OrderedCycleRepresentations H (n+2)):DirectedEdges H:=by
  refine ⟨(f.val 0,f.val 1),?_⟩
  apply (congrArg (fun G:SimpleGraph V=>G.Adj (f.val 0) (f.val 1)) f.property).mpr
  apply SimpleGraph.map_adj_apply.mpr
  rw [SimpleGraph.cycleGraph_adj]
  right
  simp

theorem orderedCycleFirstEdge_injective {V:Type} [Fintype V] [DecidableEq V] (H:SimpleGraph V)
    (n:ℕ) (hn:1≤n):Function.Injective (orderedCycleFirstEdge H n):=by
  intro f g h
  apply Subtype.ext
  apply ordered_cycle_representation_first_edge_injective (by omega)
  · exact f.property.symm.trans g.property
  · exact congrArg Prod.fst (congrArg Subtype.val h)
  · exact congrArg Prod.snd (congrArg Subtype.val h)

theorem orderedCycleFirstEdge_surjective {V:Type} [Fintype V] [DecidableEq V] (H:SimpleGraph V)
    (n:ℕ) (hH:IsEmbeddedCycle H (n+2)):Function.Surjective (orderedCycleFirstEdge H n):=by
  obtain ⟨_,f,hf⟩:=hH
  intro xy
  obtain ⟨g,hg,h0,h1⟩:=ordered_cycle_representation_first_edge_exists n f xy.val.1 xy.val.2 (by simpa [hf] using xy.property)
  refine ⟨⟨g,hf.trans hg.symm⟩,?_⟩
  apply Subtype.ext
  exact Prod.ext h0 h1

def orderedCycleFirstEdgeEquiv {V:Type} [Fintype V] [DecidableEq V] (H:SimpleGraph V)
    (n:ℕ) (hn:1≤n) (hH:IsEmbeddedCycle H (n+2)):
    OrderedCycleRepresentations H (n+2)≃DirectedEdges H:=
  Equiv.ofBijective (orderedCycleFirstEdge H n) ⟨orderedCycleFirstEdge_injective H n hn,orderedCycleFirstEdge_surjective H n hH⟩
end Oberwolfach
