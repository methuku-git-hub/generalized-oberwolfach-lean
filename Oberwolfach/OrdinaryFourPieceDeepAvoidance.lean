module

public import Oberwolfach.OrdinaryDeepBlockerLeStar
public import Oberwolfach.PhysicalWheelFamilies

@[expose] public section
/-! Four resource families preserve the deeper induced pair when the first
avoids the enclosing pair, the next two avoid the deeper pair, and the last
avoids the entire deeper star. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_four_piece_deep_avoidance
    (Q A B C D:SimpleGraph V) (H SA SB SC SD:V→U→Prop)
    (X T:Finset V) (Z W:Finset U) (hTX:T⊆X) (hWZ:W⊆Z)
    (hAsub:ordinaryPhysicalGraph A SA≤ordinaryPhysicalGraph Q H)
    (hA:Disjoint (ordinaryPhysicalGraph A SA) (spanningRestriction (ordinaryPhysicalGraph Q H) (ordinaryInnerVertices X Z)))
    (hB:Disjoint (ordinaryPhysicalGraph B SB) (ordinaryDeepBlocker T W))
    (hC:Disjoint (ordinaryPhysicalGraph C SC) (ordinaryDeepBlocker T W))
    (hD:Disjoint (ordinaryPhysicalGraph D SD) (ordinaryDeepRootStar T W)):
    Disjoint (ordinaryPhysicalGraph (((A⊔B)⊔C)⊔D) (fun v u=>((SA v u∨SB v u)∨SC v u)∨SD v u))
      (ordinaryDeepBlocker T W):=by
  have hAdeep:=ordinary_avoids_nested_deep_blocker (ordinaryPhysicalGraph Q H) (ordinaryPhysicalGraph A SA)
    X T Z W hTX hWZ hAsub hA
  have hDdeep:=hD.mono_right (ordinary_deep_blocker_le_root_star T W)
  rw [ordinaryPhysicalGraph_sup,ordinaryPhysicalGraph_sup,ordinaryPhysicalGraph_sup]
  exact disjoint_sup_left.mpr ⟨disjoint_sup_left.mpr ⟨disjoint_sup_left.mpr ⟨hAdeep,hB⟩,hC⟩,hDdeep⟩
end Oberwolfach
