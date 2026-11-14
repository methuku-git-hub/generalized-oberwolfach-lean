module

public import Oberwolfach.MarkedReferenceDeletionState
public import Oberwolfach.MarkedReservedResourceGraphs

@[expose] public section
/-! The physical graphs of a typed deletion agree with those recovered
from its removed resource set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_reference_deletion_reserved_graphs
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (D:MarkedReferenceDeletion P π d σ):
    physicalEdgeGraph (markedReservedRimPairs D.removed)=markedSampleArcSetGraph P π d σ D.arcs ∧
    markedFiniteSpokeGraph (markedReservedSpokePairs D.removed)=markedFiniteSpokeGraph D.spokes :=by
  constructor
  · ext x y
    rw [(marked_reserved_resource_graphs D.removed).1 x y]
    change (x≠y ∧ Sum.inl ({x,y}:Finset V)∈D.removed) ↔
      (x≠y ∧ ({x,y}:Finset V)∈D.arcs.image (markedPhysicalEdge (fun e=>e.val.1) (fun e=>e.val.2) (fun e=>e.val.1) (fun e=>e.val.2) π))
    simp only [MarkedReferenceDeletion.removed,markedFiniteResources,Finset.mem_union,Finset.mem_image,
      Sum.inl.injEq,Sum.inr_ne_inl,and_false,exists_false,or_false]
  · have hsp:markedReservedSpokePairs D.removed=D.spokes:=by
      ext z
      simp only [markedReservedSpokePairs,Finset.mem_filter,Finset.mem_univ,true_and,
        MarkedReferenceDeletion.removed,markedFiniteResources_spoke]
    rw [hsp]
end Oberwolfach
