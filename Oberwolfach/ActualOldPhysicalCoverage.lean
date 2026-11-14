module

public import Oberwolfach.ActualOldImageDirected

@[expose] public section
/-! Physical rim coverage of the old directed source pieces. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

def ActualOldPhysicalCoverage
    {X V K J:Type} [Fintype X] [DecidableEq X] [DecidableEq K] [DecidableEq J] [DecidableEq V]
    {F:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) F)
    (ψ:X→V) (Pack:Finset (Finset V)):Prop:=
  (∀j∈data.t,∀k<(data.C j).length,{ψ ((data.C j).getVert k),ψ ((data.C j).getVert (k+1))}∈Pack) ∧
  (∀r:SelectedRunIndex data.s₂ data.d data.T,∀k<(data.path (.inr r)).length,
    {ψ ((data.path (.inr r)).getVert k),ψ ((data.path (.inr r)).getVert (k+1))}∈Pack)
end Oberwolfach
