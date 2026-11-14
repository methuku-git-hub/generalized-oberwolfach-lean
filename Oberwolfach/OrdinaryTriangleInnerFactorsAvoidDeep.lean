module

public import Oberwolfach.OrdinaryTriangleSelectedFactorsWithHost
public import Oberwolfach.OrdinaryDeepBlockerNested

@[expose] public section
/-! If every selected inner factor avoids the deeper blocker, the completed
triangle boundary wheel family avoids that blocker as well. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I J:Type} [Fintype V] [Fintype U] [Fintype I] [Fintype J]
  [DecidableEq V] [DecidableEq U] [DecidableEq I] [DecidableEq J]

theorem ordinary_triangle_inner_factors_avoid_deep
    (R:SimpleGraph V) (S:V→U→Prop) (X T:Finset V) (Z W:Finset U)
    (hTX:T⊆X) (hWZ:W⊆Z) (hub:J→SimpleGraph (V⊕U)) (row:I→SimpleGraph (V⊕U))
    (heq:spanningRestriction (ordinaryPhysicalGraph R S) (ordinaryInnerVertices X Z)=
      (⨆j,hub j)⊔(⨆i,row i))
    (hhub:∀j,Disjoint (hub j) (ordinaryDeepBlocker T W))
    (hrow:∀i,Disjoint (row i) (ordinaryDeepBlocker T W)):
    Disjoint (ordinaryPhysicalGraph R S) (ordinaryDeepBlocker T W):=by
  apply disjoint_iff_inf_le.mpr
  intro a b hab
  obtain ⟨ha,hb⟩:=ordinary_deep_blocker_support_nested X T Z W hTX hWZ a b hab.2
  have hin:(spanningRestriction (ordinaryPhysicalGraph R S) (ordinaryInnerVertices X Z)).Adj a b:=
    (spanningRestriction_adj _ _ _ _).mpr ⟨hab.1,ha,hb⟩
  rw [heq] at hin
  rcases hin with hhub'|hrow'
  · obtain ⟨j,hj⟩:=SimpleGraph.iSup_adj.mp hhub'
    exact (disjoint_iff_inf_le.mp (hhub j)) ⟨hj,hab.2⟩
  · obtain ⟨i,hi⟩:=SimpleGraph.iSup_adj.mp hrow'
    exact (disjoint_iff_inf_le.mp (hrow i)) ⟨hi,hab.2⟩
end Oberwolfach
