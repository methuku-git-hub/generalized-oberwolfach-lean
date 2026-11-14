module

public import Oberwolfach.ActualFinalEdgesMeetInterior

@[expose] public section
/-! Deleting edges meeting a set does not change the graph induced on its
complement. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem induce_complement_delete_edges_meeting_set
    {X:Type} [Fintype X] [DecidableEq X]
    (G:SimpleGraph X) (D:Finset X) (E:Finset (Sym2 X))
    (hmeet:∀e∈E,∃x∈e.toFinset,x∈D):
    (G.deleteEdges (↑E:Set (Sym2 X))).induce {x | x∉D} = G.induce {x | x∉D}:=by
  ext x y
  change ((G.deleteEdges (↑E:Set (Sym2 X))).Adj x.1 y.1 ↔ G.Adj x.1 y.1)
  rw [SimpleGraph.deleteEdges_adj]
  constructor
  · exact And.left
  · intro h
    refine ⟨h,?_⟩
    intro he
    obtain ⟨z,hz,hzD⟩:=hmeet s(x.1,y.1) he
    have hz':z=x.1 ∨ z=y.1:=by simpa using hz
    rcases hz' with rfl|rfl
    · exact x.2 hzD
    · exact y.2 hzD
end Oberwolfach
