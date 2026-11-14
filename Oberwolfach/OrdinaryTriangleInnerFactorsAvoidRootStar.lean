module

public import Oberwolfach.OrdinaryClearedRootStarEdgeInside
public import Oberwolfach.OrdinaryTriangleSelectedFactorsRootStar

@[expose] public section
/-! Once deep-to-outside resources are cleared, inner factor avoidance
extends to the whole physical star of the deeper roots. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I J:Type} [Fintype V] [Fintype U] [Fintype I] [Fintype J]
  [DecidableEq V] [DecidableEq U] [DecidableEq I] [DecidableEq J]

theorem ordinary_triangle_inner_factors_avoid_root_star
    (R:SimpleGraph V) (S:V→U→Prop) (X T:Finset V) (Z W:Finset U)
    (hTX:T⊆X) (hWZ:W⊆Z)
    (hR:∀v∈T,∀w∉X,¬R.Adj v w) (hS:∀v∈T,∀u∉Z,¬S v u)
    (hH:∀u∈W,∀v∉X,¬S v u)
    (hub:J→SimpleGraph (V⊕U)) (row:I→SimpleGraph (V⊕U))
    (heq:spanningRestriction (ordinaryPhysicalGraph R S) (ordinaryInnerVertices X Z)=
      (⨆j,hub j)⊔(⨆i,row i))
    (hhub:∀j,Disjoint (hub j) (ordinaryDeepRootStar T W))
    (hrow:∀i,Disjoint (row i) (ordinaryDeepRootStar T W)):
    Disjoint (ordinaryPhysicalGraph R S) (ordinaryDeepRootStar T W) :=by
  apply disjoint_iff_inf_le.mpr
  intro a b hab
  obtain ⟨ha,hb⟩:=ordinary_cleared_root_star_edge_inside R S X T Z W hTX hWZ hR hS hH a b hab.1 hab.2
  have hin:(spanningRestriction (ordinaryPhysicalGraph R S) (ordinaryInnerVertices X Z)).Adj a b:=
    (spanningRestriction_adj _ _ _ _).mpr ⟨hab.1,ha,hb⟩
  rw [heq] at hin
  rcases hin with hh|hr
  · obtain ⟨j,hj⟩:=SimpleGraph.iSup_adj.mp hh
    exact (disjoint_iff_inf_le.mp (hhub j)) ⟨hj,hab.2⟩
  · obtain ⟨i,hi⟩:=SimpleGraph.iSup_adj.mp hr
    exact (disjoint_iff_inf_le.mp (hrow i)) ⟨hi,hab.2⟩
end Oberwolfach
