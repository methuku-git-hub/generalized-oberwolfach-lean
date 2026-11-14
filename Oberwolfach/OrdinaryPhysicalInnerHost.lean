module

public import Oberwolfach.OrdinaryBoundaryGraph

@[expose] public section
/-! The physical graph made from the inner rim and inner spokes is the
restriction of the original physical host to the fixed inner domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_physical_inner_host (Q:SimpleGraph V) (H:V→U→Prop) (X:Finset V) (Z:Finset U):
    ordinaryPhysicalGraph (spanningRestriction Q X) (fun v u=>H v u∧v∈X∧u∈Z)=
      spanningRestriction (ordinaryPhysicalGraph Q H) (ordinaryInnerVertices X Z):=by
  ext x y
  cases x <;> cases y <;>
    simp [ordinaryPhysicalGraph,spanningRestriction_adj,ordinaryInnerVertices_left,ordinaryInnerVertices_right,
      and_comm,and_left_comm,and_assoc]
end Oberwolfach
