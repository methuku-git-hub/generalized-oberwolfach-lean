module

public import Oberwolfach.MarkedReservedUnionSequentialIdentity

@[expose] public section
/-! Deleting first the reserved resources and then the cover-down graphs
gives the same raw sample and spoke relations as their combined deletion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]
theorem marked_reserved_union_reverse_sequential_identity
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (C:Finset (Finset V⊕(V×U))) (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)):
    let RC:=physicalEdgeGraph (markedReservedRimPairs C)
    let SC:=markedFiniteSpokeGraph (markedReservedSpokePairs C)
    let D:=DR⊔RC
    let Q:=DS⊔SC
    let edgeInst:Fintype D.edgeSet:=@SimpleGraph.fintypeEdgeSet V D (Sym2.instFintype)
      (fun x y=>Classical.propDecidable (D.Adj x y));
    rawMarkedDeleteRims σ (@SimpleGraph.edgeFinset V D edgeInst)=
      rawMarkedDeleteRims (rawMarkedDeleteRims σ RC.edgeFinset) DR.edgeFinset ∧
    markedDeletePhysicalSpokes H Q=markedDeletePhysicalSpokes (markedDeletePhysicalSpokes H SC) DS :=by
  intro RC SC D Q edgeInst
  constructor
  · have hh:=rawMarkedDeleteRims_sup σ RC DR
    have he:(@SimpleGraph.edgeFinset V D edgeInst)=(RC⊔DR).edgeFinset:=by
      ext e
      dsimp only [D]
      simp only [SimpleGraph.mem_edgeFinset,SimpleGraph.edgeSet_sup,Set.mem_union]
      exact or_comm
    rw [he]
    exact hh.symm
  · have hh:=markedDeletePhysicalSpokes_sup H SC DS
    rw [sup_comm SC DS] at hh
    exact hh.symm
end Oberwolfach
