module

public import Oberwolfach.OrdinaryTriangleInnerFactorsAvoidDeep
public import Oberwolfach.OrdinaryBoundaryRemainderLevel
public import Oberwolfach.OrdinaryProtectedHostCoverDownResult

@[expose] public section
/-! Jointly selected triangle factors which avoid the deeper blocker yield
an actual protected, balanced and divisible cover-down step. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I J:Type} [Fintype V] [Fintype U] [Fintype I] [Fintype J]
  [DecidableEq V] [DecidableEq U] [DecidableEq I] [DecidableEq J]

theorem ordinary_triangle_selected_protected_coverdown
    (Q F:SimpleGraph V) (H:V→U→Prop) (X Tdeep:Finset V) (Z Wdeep:Finset U)
    (hTX:Tdeep⊆X) (hWZ:Wdeep⊆Z) (x:I↪V) (u:J↪U)
    (hx:∀i,x i∉X) (hu:∀j,u j∉Z)
    (hxcover:∀a∉X,∃i,x i=a) (hucover:∀z∉Z,∃j,u j=z)
    (A:I→Finset V) (B:I→Finset U) (T Y:J→Finset V)
    (hA:∀i,A i⊆X) (hB:∀i,B i⊆Z) (hY:∀j,Y j⊆X)
    (hQr:∀i a,Q.Adj (x i) a↔a∈A i) (hHr:∀i z,H (x i) z↔z∈B i)
    (hHc:∀j a,H a (u j)↔a∈Y j) (hFroot:∀i,∀a∈A i,¬F.Adj (x i) a)
    (hAB:∀i,Disjoint ((A i).image Sum.inl) ((B i).image Sum.inr))
    (limit:ℝ) (C:OrdinaryTriangleSelectedFactors Q F H A B T Y hAB limit)
    (hhub:∀j,Disjoint ((localOrdinaryFactorGraph (C.hub j)).map (Function.Embedding.inl:V↪V⊕U))
      (ordinaryDeepBlocker Tdeep Wdeep))
    (hrow:∀i,Disjoint (endpointFactorGraph (hAB i) (C.row i)) (ordinaryDeepBlocker Tdeep Wdeep))
    (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,3∣(Finset.univ.filter (fun v=>H v u)).card):
    OrdinaryProtectedHostCoverDownResult Q F H X Tdeep Z Wdeep 3 limit limit :=by
  obtain ⟨R,S,hR,hS,hhost,hdec,hRsupport,hSsupport,heq⟩:=ordinary_triangle_boundary_finish_with_host
    Q F H X Z x u hx hu hxcover hucover A B T Y hA hB hY hQr hHr hHc hFroot
    C.hub C.hub_disjoint C.hub_cover C.hub_cross hAB C.row C.row_disjoint C.row_cover C.row_cross C.mixed_cross
  have hcost:∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph R S) (ordinaryInnerVertices X Z)).degree w:ℝ)≤limit:=by
    intro w;rw [heq]
    convert C.inner_degree w using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hdeep:=ordinary_triangle_inner_factors_avoid_deep R S X Tdeep Z Wdeep hTX hWZ
    (fun j=>(localOrdinaryFactorGraph (C.hub j)).map (Function.Embedding.inl:V↪V⊕U))
    (fun i=>endpointFactorGraph (hAB i) (C.row i)) heq hhub hrow
  have hdeepcost:∀w:V⊕U,((spanningRestriction (ordinaryBoundaryGraph R S Tdeep Wdeep)
      (ordinaryInnerVertices X Z)).degree w:ℝ)≤limit:=by
    intro w
    have hsub:spanningRestriction (ordinaryBoundaryGraph R S Tdeep Wdeep) (ordinaryInnerVertices X Z)≤
        spanningRestriction (ordinaryPhysicalGraph R S) (ordinaryInnerVertices X Z):=by
      intro a b hab
      have hh:=(spanningRestriction_adj _ _ _ _).mp hab
      have hb:=(ordinaryBoundaryGraph_adj _ _ _ _ _ _).mp hh.1
      exact (spanningRestriction_adj _ _ _ _).mpr ⟨hb.1,hh.2⟩
    have hh:((spanningRestriction (ordinaryBoundaryGraph R S Tdeep Wdeep) (ordinaryInnerVertices X Z)).degree w:ℝ)≤
        (spanningRestriction (ordinaryPhysicalGraph R S) (ordinaryInnerVertices X Z)).degree w:=by
      exact_mod_cast (SimpleGraph.degree_le_of_le hsub (v:=w))
    exact hh.trans (hcost w)
  have hrem:=ordinary_boundary_decomposition_remainder_level Q R H S 3 X Z limit hR hS hdec hbal hdiv hRsupport hSsupport hcost
  exact ⟨R,S,hR,hS,hhost,hrem.2.2.2.2.1,hrem.2.2.1,hrem.2.2.2.1,hcost,hdeepcost,hdeep⟩
end Oberwolfach
