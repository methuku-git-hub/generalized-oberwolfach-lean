module

public import Oberwolfach.ActualMatchedPieceDirectedArcs

@[expose] public section
/-! Directed-image property of the actual selected source cycles and runs. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

def ActualOldImageDirected
    {X V K J:Type} [Fintype X] [DecidableEq X] [DecidableEq K] [DecidableEq J]
    {G:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) G) (ψ:X→V) (R:V→V→Prop):Prop:=
  (∀j∈data.t,∀k<(data.C j).length,R (ψ ((data.C j).getVert k)) (ψ ((data.C j).getVert (k+1)))) ∧
  (∀r:SelectedRunIndex data.s₂ data.d data.T,∀k<(data.path (.inr r)).length,
    R (ψ ((data.path (.inr r)).getVert k)) (ψ ((data.path (.inr r)).getVert (k+1))))
end Oberwolfach
