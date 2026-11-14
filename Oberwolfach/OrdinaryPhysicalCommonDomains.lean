module

public import Oberwolfach.OrdinaryEndpointPhysicalGeometry

@[expose] public section
/-! Exact common-neighborhood identities on the disjoint rim and hub
domains of the physical graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_physical_common_rim (G:SimpleGraph V) (A S:Finset V):
    common (A.image (Sum.inl:V→V⊕U)) (S.image Sum.inl)
      (fun z=>(ordinaryPhysicalGraph G (fun _ _=>False)).neighborFinset z)=
    (common A S (fun z=>G.neighborFinset z)).image Sum.inl:=by
  ext z
  cases z <;> simp [common,ordinaryPhysicalGraph,SimpleGraph.mem_neighborFinset]

theorem ordinary_physical_common_spoke_rows (H:V→U→Prop) (A:Finset V) (J:Finset U):
    common (A.image (Sum.inl:V→V⊕U)) (J.image Sum.inr)
      (fun z=>(ordinaryPhysicalGraph ⊥ H).neighborFinset z)=
    (common A J (fun u=>Finset.univ.filter (fun v=>H v u))).image Sum.inl:=by
  ext z
  cases z <;> simp [common,ordinaryPhysicalGraph,SimpleGraph.mem_neighborFinset]

theorem ordinary_physical_common_spoke_hubs (H:V→U→Prop) (B:Finset U) (S:Finset V):
    common (B.image (Sum.inr:U→V⊕U)) (S.image Sum.inl)
      (fun z=>(ordinaryPhysicalGraph ⊥ H).neighborFinset z)=
    (common B S (fun v=>Finset.univ.filter (H v))).image Sum.inr:=by
  ext z
  cases z <;> simp [common,ordinaryPhysicalGraph,SimpleGraph.mem_neighborFinset]
end Oberwolfach
