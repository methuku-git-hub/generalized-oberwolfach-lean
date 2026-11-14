module

public import Oberwolfach.EndpointHostGraph
public import Oberwolfach.OrdinaryBoundaryRootSets

@[expose] public section
/-! The endpoint-factor host and its root classes are exactly the inner
rim/spoke graph and canonical boundary classes on separate vertex types. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_endpoint_host_physical_geometry (Q:SimpleGraph V) (H:V→U→Prop)
    (X:Finset V) (Z:Finset U):
    endpointHostGraph (ordinaryPhysicalGraph Q (fun _ _=>False)) (ordinaryPhysicalGraph ⊥ H)
      (X.image Sum.inl) (Z.image Sum.inr)=
      ordinaryPhysicalGraph (spanningRestriction Q X) (fun v u=>H v u∧v∈X∧u∈Z):=by
  ext a b
  cases a with
  | inl v=>cases b with
    | inl w=>simp [endpointHostGraph,ordinaryPhysicalGraph,spanningRestriction_adj] <;> tauto
    | inr u=>simp [endpointHostGraph,ordinaryPhysicalGraph] <;> tauto
  | inr u=>cases b with
    | inl v=>simp [endpointHostGraph,ordinaryPhysicalGraph,and_comm,and_left_comm]
    | inr u'=>simp [endpointHostGraph,ordinaryPhysicalGraph]

theorem ordinary_endpoint_row_domain (Q:SimpleGraph V) (X:Finset V) (i:{v:V // v∉X}):
    common (X.image (Sum.inl:V→V⊕U)) {Sum.inl i.val}
      (fun y=>(ordinaryPhysicalGraph (U:=U) Q (fun _ _=>False)).neighborFinset y)=
      (ordinaryBoundaryRimSet Q X i).image Sum.inl:=by
  ext a
  cases a with
  | inl v=>simp [common,ordinaryBoundaryRimSet,ordinaryPhysicalGraph,SimpleGraph.mem_neighborFinset,Q.adj_comm] <;> tauto
  | inr u=>simp [common,ordinaryBoundaryRimSet,ordinaryPhysicalGraph,SimpleGraph.mem_neighborFinset]

theorem ordinary_endpoint_index_domain (H:V→U→Prop) (X:Finset V) (Z:Finset U) (i:{v:V // v∉X}):
    common (Z.image Sum.inr) {Sum.inl i.val}
      (fun y=>(ordinaryPhysicalGraph ⊥ H).neighborFinset y)=
      (ordinaryBoundaryRowSet H X Z i).image Sum.inr:=by
  ext a
  cases a with
  | inl v=>simp [common,ordinaryBoundaryRowSet,ordinaryPhysicalGraph,SimpleGraph.mem_neighborFinset]
  | inr u=>simp [common,ordinaryBoundaryRowSet,ordinaryPhysicalGraph,SimpleGraph.mem_neighborFinset]
end Oberwolfach
