module

public import Oberwolfach.OrdinaryBoundaryGraph

@[expose] public section
/-! Changes of boundary classes are charged to the uncovered unreserved
graph and the later cleanup, at each physical vertex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_boundary_outside_inner (Q:SimpleGraph V) (H:V→U→Prop) (X:Finset V) (Z:Finset U):
    ordinaryBoundaryGraph Q H X Z≤
      ordinaryPhysicalGraph Q H\spanningRestriction (ordinaryPhysicalGraph Q H) (ordinaryInnerVertices X Z):=by
  intro a b hab
  have hh:=(ordinaryBoundaryGraph_adj Q H X Z a b).mp hab
  refine ⟨hh.1,?_⟩
  intro hi
  have hin:=(spanningRestriction_adj _ _ _ _).mp hi
  rcases hh.2 with ⟨ha,_⟩|⟨hb,_⟩
  · exact ha hin.2.1
  · exact hb hin.2.2

theorem ordinary_boundary_change_degree_after_packings
    (Q:SimpleGraph V) (H:V→U→Prop) (X:Finset V) (Z:Finset U)
    (C D:SimpleGraph (V⊕U)) (σ:Sym2 (V⊕U)→Bool) (τ δ:ℝ)
    (hrem:∀w,((((ordinaryPhysicalGraph Q H\spanningRestriction (ordinaryPhysicalGraph Q H)
      (ordinaryInnerVertices X Z))\retainedGraph (ordinaryBoundaryGraph Q H X Z) σ)\C).degree w:ℝ)≤τ)
    (hD:∀w,(D.degree w:ℝ)≤δ):
    ∀w,(((ordinaryBoundaryGraph Q H X Z\retainedGraph (ordinaryBoundaryGraph Q H X Z) σ)\C).degree w:ℝ)+
      (D.degree w:ℝ)≤τ+δ:=by
  have hsub:((ordinaryBoundaryGraph Q H X Z\retainedGraph (ordinaryBoundaryGraph Q H X Z) σ)\C)≤
      ((ordinaryPhysicalGraph Q H\spanningRestriction (ordinaryPhysicalGraph Q H) (ordinaryInnerVertices X Z))\
        retainedGraph (ordinaryBoundaryGraph Q H X Z) σ)\C:=by
    intro a b hab
    exact ⟨⟨ordinary_boundary_outside_inner Q H X Z hab.1.1,hab.1.2⟩,hab.2⟩
  intro w
  have hh:((((ordinaryBoundaryGraph Q H X Z\retainedGraph (ordinaryBoundaryGraph Q H X Z) σ)\C).degree w):ℝ)≤
      (((((ordinaryPhysicalGraph Q H\spanningRestriction (ordinaryPhysicalGraph Q H)
        (ordinaryInnerVertices X Z))\retainedGraph (ordinaryBoundaryGraph Q H X Z) σ)\C).degree w):ℝ):=by
    exact_mod_cast (SimpleGraph.degree_le_of_le hsub (v:=w))
  linarith only [hh,hrem w,hD w]
end Oberwolfach
