module

public import Oberwolfach.OrdinaryPhysicalCommonDomains

@[expose] public section
/-! Graph difference on rim-only physical graphs is the physical image of
the original rim graph difference. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_physical_rim_difference (P F:SimpleGraph V):
    (ordinaryPhysicalGraph (U:=U) P (fun _ _=>False))\(ordinaryPhysicalGraph F (fun _ _=>False))=
    ordinaryPhysicalGraph (P\F) (fun _ _=>False):=by
  ext x y
  cases x <;> cases y <;> simp [ordinaryPhysicalGraph,SimpleGraph.sdiff_adj]
end Oberwolfach
