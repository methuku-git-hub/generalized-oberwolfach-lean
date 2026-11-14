module

public import Oberwolfach.OrdinaryBoundaryRemainderLevel

@[expose] public section
/-! The selected triangle and hub factors produce an actual balanced,
divisible next-level remainder with the claimed inner cost. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I J:Type} [Fintype V] [Fintype U] [Fintype I] [Fintype J]
  [DecidableEq V] [DecidableEq U] [DecidableEq I] [DecidableEq J]

theorem ordinary_triangle_selected_factors_next_level (Q F:SimpleGraph V) (H:V→U→Prop)
    (X:Finset V) (Z:Finset U) (x:I↪V) (u:J↪U)
    (hx:∀i,x i∉X) (hu:∀j,u j∉Z)
    (hxcover:∀a∉X,∃i,x i=a) (hucover:∀z∉Z,∃j,u j=z)
    (A:I→Finset V) (B:I→Finset U) (T Y:J→Finset V)
    (hA:∀i,A i⊆X) (hB:∀i,B i⊆Z) (hY:∀j,Y j⊆X)
    (hQr:∀i a,Q.Adj (x i) a↔a∈A i) (hHr:∀i z,H (x i) z↔z∈B i)
    (hHc:∀j a,H a (u j)↔a∈Y j) (hFroot:∀i,∀a∈A i,¬F.Adj (x i) a)
    (hAB:∀i,Disjoint ((A i).image Sum.inl) ((B i).image Sum.inr))
    (limit:ℝ) (C:OrdinaryTriangleSelectedFactors Q F H A B T Y hAB limit)
    (hQbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hQdiv:∀u,3∣(Finset.univ.filter (fun v=>H v u)).card):
    ∃R:SimpleGraph V,∃S:V→U→Prop,
      R≤Q ∧ (∀v u,S v u→H v u) ∧ HasOrdinaryWheelDecomposition R S 3 ∧
      let Q':=Q\R;let H':=fun v u=>H v u∧¬S v u;
      Q'≤spanningRestriction Q X ∧ (∀v u,H' v u→H v u∧v∈X∧u∈Z) ∧
      (∀v,Q'.degree v=2*(Finset.univ.filter (H' v)).card) ∧
      (∀u,3∣(Finset.univ.filter (fun v=>H' v u)).card) ∧
      ordinaryHostResources Q' H'⊆ordinaryRootResources X Z ∧
      (∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph R S) (ordinaryInnerVertices X Z)).degree w:ℝ)≤limit):=by
  obtain ⟨R,S,hR,hS,hdec,hRsupport,hSsupport,hcost⟩:=ordinary_triangle_finish_from_selected_factors
    Q F H X Z x u hx hu hxcover hucover A B T Y hA hB hY hQr hHr hHc hFroot hAB limit C
  have h:=ordinary_boundary_decomposition_remainder_level Q R H S 3 X Z limit hR hS hdec hQbal hQdiv hRsupport hSsupport hcost
  exact ⟨R,S,hR,hS,hdec,h⟩
end Oberwolfach
