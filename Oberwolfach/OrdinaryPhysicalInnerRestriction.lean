module

public import Oberwolfach.OrdinaryBoundaryGraph

@[expose] public section
/-! The typed restriction used by the fresh factor event is exactly the
protected physical inner host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_physical_inner_restriction
    (Q:SimpleGraph V) (H:V→U→Prop) (X:Finset V) (Z:Finset U):
    ordinaryPhysicalGraph (spanningRestriction Q X) (fun v u=>H v u∧v∈X∧u∈Z)=
      spanningRestriction (ordinaryPhysicalGraph Q H) (ordinaryInnerVertices X Z):=by
  ext a b
  rw [spanningRestriction_adj]
  cases a <;> cases b <;>
    simp only [ordinaryPhysicalGraph,spanningRestriction_adj,ordinaryInnerVertices_left,ordinaryInnerVertices_right] <;> tauto
end Oberwolfach
