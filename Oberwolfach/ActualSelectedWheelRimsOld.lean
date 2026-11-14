module

public import Oberwolfach.ActualMatchedWheelRimsOld

@[expose] public section
/-! The selected wheel family has all its physical rim edges in the actual
old edge image. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def ActualSelectedWheelRimsOld
    {X V U E L K J:Type} [Fintype X] [DecidableEq X] [DecidableEq V] [DecidableEq U] [DecidableEq K] [DecidableEq J]
    {F:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) F) (ψ:X→V)
    (tail head:E→V) (ktail khead:L→V) (m b:ℕ) (π:Equiv.Perm V) (H₀ Hₖ:V→U→Prop)
    (W:actualSelectedSegmentIndex data→MarkedWheel tail head ktail khead m π b H₀ Hₖ):Prop:=
  ∀z edge,edge∈markedCyclePhysicalEdges tail head ktail khead m π b (W z).1→
    ∃e∈(data.deletedEdges\(Finset.univ.biUnion (fun i:{i // i∈data.s₁}=>(data.path (.inl i)).edges.toFinset))).image (Sym2.map ψ),e.toFinset=edge
end Oberwolfach
