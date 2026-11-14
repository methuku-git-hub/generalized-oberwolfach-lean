module

public import Oberwolfach.OrdinaryTriangleBoundaryFinishBounded

@[expose] public section
/-! A single record keeps the actual jointly selected triangle endpoint and
hub factors, their disjointness, coverage and inner-degree budget. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I J:Type} [Fintype V] [Fintype U] [Fintype I] [Fintype J]
  [DecidableEq V] [DecidableEq U] [DecidableEq I] [DecidableEq J]

structure OrdinaryTriangleSelectedFactors (Q F:SimpleGraph V) (H:V→U→Prop)
    (A:I→Finset V) (B:I→Finset U) (T Y:J→Finset V)
    (hAB:∀i,Disjoint ((A i).image Sum.inl) ((B i).image Sum.inr)) (limit:ℝ) where
  hub:∀j,Finset (LocalOrdinaryCycle Q F (T j) 3)
  hub_disjoint:∀j,∀C∈hub j,∀C'∈hub j,C≠C'→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices C')
  hub_cover:∀j,(hub j).biUnion localOrdinaryVertices=Y j
  hub_cross:∀i j,i≠j→Disjoint (localOrdinaryFactorGraph (hub i)) (localOrdinaryFactorGraph (hub j))
  row:∀i,Finset (EndpointTriangle (ordinaryPhysicalGraph Q H) (ordinaryPhysicalGraph F (fun _ _=>False))
    ((A i).image Sum.inl) ((B i).image Sum.inr))
  row_disjoint:∀i,∀C∈row i,∀C'∈row i,C≠C'→Disjoint C.val C'.val
  row_cover:∀i,(row i).biUnion endpointTriangleVertices=(A i).image Sum.inl∪(B i).image Sum.inr
  row_cross:∀i j,i≠j→Disjoint (endpointFactorGraph (hAB i) (row i)) (endpointFactorGraph (hAB j) (row j))
  mixed_cross:∀j i,Disjoint ((localOrdinaryFactorGraph (hub j)).map (Function.Embedding.inl:V↪V⊕U))
    (endpointFactorGraph (hAB i) (row i))
  inner_degree:∀w:V⊕U,(((⨆j,(localOrdinaryFactorGraph (hub j)).map (Function.Embedding.inl:V↪V⊕U))⊔
    (⨆i,endpointFactorGraph (hAB i) (row i))).degree w:ℝ)≤limit

theorem ordinary_triangle_finish_from_selected_factors (Q F:SimpleGraph V) (H:V→U→Prop)
    (X:Finset V) (Z:Finset U) (x:I↪V) (u:J↪U)
    (hx:∀i,x i∉X) (hu:∀j,u j∉Z)
    (hxcover:∀a∉X,∃i,x i=a) (hucover:∀z∉Z,∃j,u j=z)
    (A:I→Finset V) (B:I→Finset U) (T Y:J→Finset V)
    (hA:∀i,A i⊆X) (hB:∀i,B i⊆Z) (hY:∀j,Y j⊆X)
    (hQr:∀i a,Q.Adj (x i) a↔a∈A i)
    (hHr:∀i z,H (x i) z↔z∈B i)
    (hHc:∀j a,H a (u j)↔a∈Y j)
    (hFroot:∀i,∀a∈A i,¬F.Adj (x i) a)
    (hAB:∀i,Disjoint ((A i).image Sum.inl) ((B i).image Sum.inr))
    (limit:ℝ) (C:OrdinaryTriangleSelectedFactors Q F H A B T Y hAB limit):
    ∃R:SimpleGraph V,∃S:V→U→Prop,
      R≤Q ∧ (∀a z,S a z→H a z) ∧ HasOrdinaryWheelDecomposition R S 3 ∧
      (Q\R).support⊆(X:Set V) ∧
      (∀a z,H a z∧¬S a z→a∈X∧z∈Z) ∧
      (∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph R S) (ordinaryInnerVertices X Z)).degree w:ℝ)≤limit):=by
  obtain ⟨R,S,hR,hS,hdec,houtR,houtS,_,hdeg⟩:=ordinary_triangle_boundary_finish_bounded Q F H X Z x u hx hu hxcover hucover
    A B T Y hA hB hY hQr hHr hHc hFroot C.hub C.hub_disjoint C.hub_cover C.hub_cross hAB
    C.row C.row_disjoint C.row_cover C.row_cross C.mixed_cross limit C.inner_degree
  exact ⟨R,S,hR,hS,hdec,houtR,houtS,hdeg⟩
end Oberwolfach
