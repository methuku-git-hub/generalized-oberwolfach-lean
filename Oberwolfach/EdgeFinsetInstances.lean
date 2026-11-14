module

public import Oberwolfach.ResidualActualData

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem edge_finset_card_independent {V:Type} (G:SimpleGraph V) (A B:Fintype G.edgeSet):
    (@SimpleGraph.edgeFinset V G A).card=(@SimpleGraph.edgeFinset V G B).card := by
  congr 1
  apply Finset.coe_injective
  exact (@SimpleGraph.coe_edgeFinset V G A).trans (@SimpleGraph.coe_edgeFinset V G B).symm
end Oberwolfach
