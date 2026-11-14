module

public import Oberwolfach.OrdinaryBoundaryPairMap
public import Oberwolfach.GraphSpanningRestrictionMap
public import Oberwolfach.OrdinaryMappedLeftoverDegrees
public import Oberwolfach.OrdinaryProtectedInnerPersistence
public import Oberwolfach.OrdinaryDeepBlockerNested

@[expose] public section
/-! A protected local wheel family keeps both degree costs and deep-pair
avoidance when embedded in the ambient host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U V' U':Type} [Fintype V] [Fintype U] [Fintype V'] [Fintype U']
  [DecidableEq V] [DecidableEq U] [DecidableEq V'] [DecidableEq U']

theorem ordinary_mapped_protected_costs
    (D:SimpleGraph V) (E:V→U→Prop) (X T:Finset V) (Z W:Finset U)
    (φ:V↪V') (ψ:U↪U') (cost deepCost:ℝ) (hc0:0≤cost) (hd0:0≤deepCost)
    (hcost:∀a:V⊕U,((spanningRestriction (ordinaryPhysicalGraph D E) (ordinaryInnerVertices X Z)).degree a:ℝ)≤cost)
    (hdeep:∀a:V⊕U,((spanningRestriction (ordinaryBoundaryGraph D E T W) (ordinaryInnerVertices X Z)).degree a:ℝ)≤deepCost)
    (havoid:Disjoint (ordinaryPhysicalGraph D E) (ordinaryDeepBlocker T W)):
    (∀a:V'⊕U',((spanningRestriction (ordinaryPhysicalGraph (D.map φ) (ordinaryMappedSpokes E φ ψ))
      (ordinaryInnerVertices (X.image φ) (Z.image ψ))).degree a:ℝ)≤cost) ∧
    (∀a:V'⊕U',((spanningRestriction (ordinaryBoundaryGraph (D.map φ) (ordinaryMappedSpokes E φ ψ)
      (T.image φ) (W.image ψ)) (ordinaryInnerVertices (X.image φ) (Z.image ψ))).degree a:ℝ)≤deepCost) ∧
    Disjoint (ordinaryPhysicalGraph (D.map φ) (ordinaryMappedSpokes E φ ψ))
      (ordinaryDeepBlocker (T.image φ) (W.image ψ)):=by
  let e:=φ.sumMap ψ
  have he:spanningRestriction (ordinaryPhysicalGraph (D.map φ) (ordinaryMappedSpokes E φ ψ))
      (ordinaryInnerVertices (X.image φ) (Z.image ψ))=
      (spanningRestriction (ordinaryPhysicalGraph D E) (ordinaryInnerVertices X Z)).map e:=by
    rw [ordinary_physical_pair_map,←ordinary_inner_vertices_image,←graph_spanning_restriction_map]
  have hd:spanningRestriction (ordinaryBoundaryGraph (D.map φ) (ordinaryMappedSpokes E φ ψ)
      (T.image φ) (W.image ψ)) (ordinaryInnerVertices (X.image φ) (Z.image ψ))=
      (spanningRestriction (ordinaryBoundaryGraph D E T W) (ordinaryInnerVertices X Z)).map e:=by
    rw [ordinary_boundary_pair_map,←ordinary_inner_vertices_image,←graph_spanning_restriction_map]
  have hcmap:=ordinary_graph_map_degree_bound (spanningRestriction (ordinaryPhysicalGraph D E) (ordinaryInnerVertices X Z)) e cost hc0 hcost
  have hdmap:=ordinary_graph_map_degree_bound (spanningRestriction (ordinaryBoundaryGraph D E T W) (ordinaryInnerVertices X Z)) e deepCost hd0 hdeep
  have hz:spanningRestriction (ordinaryPhysicalGraph (D.map φ) (ordinaryMappedSpokes E φ ψ))
      (ordinaryInnerVertices (T.image φ) (W.image ψ))=⊥:=by
    rw [ordinary_physical_pair_map,←ordinary_inner_vertices_image,←graph_spanning_restriction_map,
      ordinary_protected_inner_zero D E T W havoid]
    ext a b
    simp only [SimpleGraph.bot_adj,iff_false]
    intro hab
    obtain ⟨x,y,hxy,_,_⟩:=(SimpleGraph.map_adj (φ.sumMap ψ) (⊥:SimpleGraph (V⊕U)) a b).mp hab
    exact hxy
  refine ⟨?_,?_,?_⟩
  · intro a
    have hh:=hcmap a
    have hx:=congrArg (fun G:SimpleGraph (V'⊕U')=>(G.degree a:ℝ)) he
    have hx':((spanningRestriction (ordinaryPhysicalGraph (D.map φ) (ordinaryMappedSpokes E φ ψ))
        (ordinaryInnerVertices (X.image φ) (Z.image ψ))).degree a:ℝ)=
        (((spanningRestriction (ordinaryPhysicalGraph D E) (ordinaryInnerVertices X Z)).map e).degree a:ℝ):=by
      convert hx using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
    exact hx'.le.trans hh
  · intro a
    have hh:=hdmap a
    have hx:=congrArg (fun G:SimpleGraph (V'⊕U')=>(G.degree a:ℝ)) hd
    have hx':((spanningRestriction (ordinaryBoundaryGraph (D.map φ) (ordinaryMappedSpokes E φ ψ)
        (T.image φ) (W.image ψ)) (ordinaryInnerVertices (X.image φ) (Z.image ψ))).degree a:ℝ)=
        (((spanningRestriction (ordinaryBoundaryGraph D E T W) (ordinaryInnerVertices X Z)).map e).degree a:ℝ):=by
      convert hx using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
    exact hx'.le.trans hh
  · apply disjoint_iff_inf_le.mpr
    intro a b hab
    obtain ⟨ha,hb⟩:=ordinary_deep_blocker_support_nested (T.image φ) (T.image φ) (W.image ψ) (W.image ψ)
      (Finset.Subset.refl _) (Finset.Subset.refl _) a b hab.2
    have hi:(spanningRestriction (ordinaryPhysicalGraph (D.map φ) (ordinaryMappedSpokes E φ ψ))
        (ordinaryInnerVertices (T.image φ) (W.image ψ))).Adj a b:=
      (spanningRestriction_adj _ _ _ _).mpr ⟨hab.1,ha,hb⟩
    rw [hz] at hi
    exact hi
end Oberwolfach
