module

public import Oberwolfach.OrdinaryProtectedInnerPersistence

@[expose] public section
/-! Equality of physical graphs on an enclosing pair also preserves every
boundary graph restricted to that pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_boundary_restriction_of_physical_restriction
    (Q Q':SimpleGraph V) (H H':V→U→Prop) (X T:Finset V) (Z W:Finset U)
    (hphys:spanningRestriction (ordinaryPhysicalGraph Q H) (ordinaryInnerVertices X Z)=
      spanningRestriction (ordinaryPhysicalGraph Q' H') (ordinaryInnerVertices X Z)):
    spanningRestriction (ordinaryBoundaryGraph Q H T W) (ordinaryInnerVertices X Z)=
      spanningRestriction (ordinaryBoundaryGraph Q' H' T W) (ordinaryInnerVertices X Z):=by
  ext a b
  simp only [spanningRestriction_adj,ordinaryBoundaryGraph_adj]
  constructor
  · rintro ⟨⟨hab,hcross⟩,ha,hb⟩
    have hi:(spanningRestriction (ordinaryPhysicalGraph Q H) (ordinaryInnerVertices X Z)).Adj a b:=
      (spanningRestriction_adj _ _ _ _).mpr ⟨hab,ha,hb⟩
    rw [hphys] at hi
    exact ⟨⟨((spanningRestriction_adj _ _ _ _).mp hi).1,hcross⟩,ha,hb⟩
  · rintro ⟨⟨hab,hcross⟩,ha,hb⟩
    have hi:(spanningRestriction (ordinaryPhysicalGraph Q' H') (ordinaryInnerVertices X Z)).Adj a b:=
      (spanningRestriction_adj _ _ _ _).mpr ⟨hab,ha,hb⟩
    rw [←hphys] at hi
    exact ⟨⟨((spanningRestriction_adj _ _ _ _).mp hi).1,hcross⟩,ha,hb⟩
end Oberwolfach
