module

public import Oberwolfach.OrdinaryBoundaryRootSets

@[expose] public section
/-! The factor host used after localization is exactly the original physical
host restricted to the inner rim and hub domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_inner_factor_host_eq (Q:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (B:Finset U):
    ordinaryPhysicalGraph (spanningRestriction Q A) (fun v u=>H v u∧v∈A∧u∈B)=
      spanningRestriction (ordinaryPhysicalGraph Q H) (ordinaryInnerVertices A B):=by
  ext x y
  cases x with
  | inl v=>cases y with
    | inl w=>simp [ordinaryPhysicalGraph,spanningRestriction_adj,ordinaryInnerVertices_left]
    | inr u=>simp [ordinaryPhysicalGraph,spanningRestriction_adj,ordinaryInnerVertices_left,ordinaryInnerVertices_right]
  | inr u=>cases y with
    | inl v=>simp [ordinaryPhysicalGraph,spanningRestriction_adj,ordinaryInnerVertices_left,ordinaryInnerVertices_right,and_comm,and_left_comm]
    | inr u'=>simp [ordinaryPhysicalGraph,spanningRestriction_adj,ordinaryInnerVertices_right]
end Oberwolfach
