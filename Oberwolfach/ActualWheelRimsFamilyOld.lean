module

public import Oberwolfach.ActualSelectedWheelRimsOld

@[expose] public section
/-! All rims of a finite marked wheel family lie in the old physical edge
image. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def ActualWheelRimsFamilyOld
    {X V U E L K J:Type} [Fintype X] [DecidableEq X] [DecidableEq V] [DecidableEq U] [DecidableEq K] [DecidableEq J]
    {F:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) F) (ψ:X→V)
    (tail head:E→V) (ktail khead:L→V) (m b:ℕ) (π:Equiv.Perm V) (H₀ Hₖ:V→U→Prop)
    (S:Finset (MarkedWheel tail head ktail khead m π b H₀ Hₖ)):Prop:=
  ∀W∈S,∀edge,edge∈markedCyclePhysicalEdges tail head ktail khead m π b W.1→
    ∃e∈(data.deletedEdges\(Finset.univ.biUnion (fun i:{i // i∈data.s₁}=>(data.path (.inl i)).edges.toFinset))).image (Sym2.map ψ),e.toFinset=edge
end Oberwolfach
