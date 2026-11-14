module

public import Oberwolfach.MarkedPhysicalDeletionComposition
public import Oberwolfach.MarkedReservedResourceGraphs

@[expose] public section
/-! The combined first and reserved physical deletions agree with their
sequential application on every raw rim coordinate and both spoke types. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_reserved_union_sequential_identity
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (C:Finset (Finset V⊕(V×U))) (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)):
    let RC:=physicalEdgeGraph (markedReservedRimPairs C)
    let SC:=markedFiniteSpokeGraph (markedReservedSpokePairs C)
    let D:=DR⊔RC
    let Q:=DS⊔SC
    let edgeInst:Fintype D.edgeSet:=@SimpleGraph.fintypeEdgeSet V D (Sym2.instFintype)
      (fun x y=>Classical.propDecidable (D.Adj x y));
    rawMarkedDeleteRims σ (@SimpleGraph.edgeFinset V D edgeInst)=
      rawMarkedDeleteRims (rawMarkedDeleteRims σ DR.edgeFinset) RC.edgeFinset ∧
    markedDeletePhysicalSpokes H Q=markedDeletePhysicalSpokes (markedDeletePhysicalSpokes H DS) SC :=by
  intro RC SC D Q edgeInst
  constructor
  · have hh:=rawMarkedDeleteRims_sup σ DR RC
    convert hh.symm using 1 <;> congr!
  · exact (markedDeletePhysicalSpokes_sup H DS SC).symm
end Oberwolfach
