module

public import Oberwolfach.MarkedPhysicalEdges
public import Oberwolfach.PhysicalEdgeGraph

@[expose] public section
/-! The ordinary and marked physical arcs are edges of the graph formed
from their physical images, assuming the manuscript's looplessness. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def markedPhysicalRimSet {V E K:Type*} [DecidableEq V] [Fintype E] [Fintype K]
    (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V):Finset (Finset V):=
  Finset.univ.image (markedPhysicalEdge tail head ktail khead π)

theorem marked_physical_host_graph_inputs
    {V E K:Type*} [Fintype V] [DecidableEq V] [Fintype E] [Fintype K]
    (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V)
    (hE:∀e:E,tail e≠head e) (hK:∀e:K,ktail e≠π (khead e)):
    (∀e:E,(physicalEdgeGraph (markedPhysicalRimSet tail head ktail khead π)).Adj (tail e) (head e)) ∧
    (∀e:K,(physicalEdgeGraph (markedPhysicalRimSet tail head ktail khead π)).Adj (ktail e) (π (khead e))) := by
  constructor
  · intro e
    refine ⟨hE e,?_⟩
    exact Finset.mem_image.mpr ⟨Sum.inl e,Finset.mem_univ _,rfl⟩
  · intro e
    refine ⟨hK e,?_⟩
    exact Finset.mem_image.mpr ⟨Sum.inr e,Finset.mem_univ _,rfl⟩
end Oberwolfach
