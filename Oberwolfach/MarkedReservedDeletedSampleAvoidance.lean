module

public import Oberwolfach.MarkedReservedResourceGraphs
public import Oberwolfach.MarkedSamplePhysicalDeletionLift

@[expose] public section
/-! Every wheel in a sampled host from which the reserved physical graphs
were deleted avoids the reserved resources. This is independent of how the
wheel was selected. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_deleted_sample_packing_avoids_reserved_resources
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (hm:1≤m) (hb:1≤3*d)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (C:Finset (Finset V⊕(V×U))) (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U))
    (hR:physicalEdgeGraph (markedReservedRimPairs C)≤DR)
    (hS:markedFiniteSpokeGraph (markedReservedSpokePairs C)≤DS)
    (M:Finset (MarkedPhysicalDeletedSampleWheel P π d m σ DR DS H)):
    Disjoint C (M.biUnion markedWheelPhysicalResources):=by
  apply Finset.disjoint_left.mpr
  intro e hC hM
  obtain ⟨W,hW,he⟩:=Finset.mem_biUnion.mp hM
  have hav:=markedPhysicalDeletedSampleWheel_avoids P π d m σ DR DS H W
  cases e with
  | inr z=>
    have hgraph:DS.Adj (Sum.inl z.1) (Sum.inr z.2):=hS (((marked_reserved_resource_graphs C).2.1 z.1 z.2).mpr hC)
    exact hav.2 z.1 z.2 he hgraph
  | inl e=>
    have he':e∈markedCyclePhysicalEdges _ _ _ _ m π (3*d) W.1:=
      (markedWheelPhysicalResources_rim W e).mp he
    have hcard:e.card=2:=by
      obtain ⟨i,_,hi⟩:=Finset.mem_image.mp he'
      rw [←hi]
      exact markedCycle_physical_edge_card _ _ _ _ m π (3*d) hm hb W.1 i
    obtain ⟨x,y,hxy,rfl⟩:=Finset.card_eq_two.mp hcard
    have hgraph:DR.Adj x y:=hR (((marked_reserved_resource_graphs C).1 x y).mpr ⟨hxy,hC⟩)
    exact hav.1 x y he' hgraph
end Oberwolfach
