module

public import Oberwolfach.ActualSelectedWheelRimsOld

@[expose] public section
/-! The assigned ordinary wheel rims belong to the same old edge image. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def ActualAssignedOrdinaryRimsOld
    {X V K J I:Type} [Fintype X] [DecidableEq X] [DecidableEq V] [DecidableEq K] [DecidableEq J]
    {F:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) F) (ψ:X→V)
    (r:I→ℕ) (q:∀i,Fin (r i)→V):Prop:=
  ∀i k,s(q i k,q i (cycleNext k))∈
    (data.deletedEdges\(Finset.univ.biUnion (fun j:{j // j∈data.s₁}=>(data.path (.inl j)).edges.toFinset))).image (Sym2.map ψ)
end Oberwolfach
