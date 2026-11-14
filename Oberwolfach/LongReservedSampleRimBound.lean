module

public import Oberwolfach.MarkedResourceRimCardinality
public import Oberwolfach.LongReservedRimContainedInClass

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_reserved_sample_rim_bounded
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (D:Finset (Sym2 V)) (B:ℕ):
    let raw:RawMarkedOutcome V U Γ Color:=fun e=>rawExpandedMarkedCollapse e (ω e)
    let σ':=rawMarkedDeleteRims raw D
    let E':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true;
    ∀C:MarkedSupportedEdgeSet (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) π U,
    C.edges.card≤B→
      markedResourceRimGraph C.edges≤longPhysicalStateGraph P ω {0,1,2,3,4} ∧
      (markedResourceRimGraph C.edges).edgeFinset.card≤B := by
  intro raw σ' E' K' C hC
  have hsub:markedResourceRimGraph C.edges≤longPhysicalStateGraph P ω {0,1,2,3,4}:=
    (long_reserved_sample_rim_contained_in_class P (longPhysicalStateGraph P ω {0,1,2,3,4}) ⊥ π d ω D C
      (by intro x y h; rfl)).1
  exact ⟨hsub,(marked_resource_rim_graph_edge_card_le C.edges).trans hC⟩
end Oberwolfach
