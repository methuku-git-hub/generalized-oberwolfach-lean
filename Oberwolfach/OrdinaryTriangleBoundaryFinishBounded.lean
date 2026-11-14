module

public import Oberwolfach.OrdinaryTriangleBoundaryFinish

@[expose] public section
/-! The selected triangle factors cover every boundary edge while the
combined factor-graph bound controls the resources spent inside. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I J:Type} [Fintype V] [Fintype U] [Fintype I] [Fintype J]
  [DecidableEq V] [DecidableEq U] [DecidableEq I] [DecidableEq J]

theorem ordinary_triangle_boundary_finish_bounded (Q F:SimpleGraph V) (H:V→U→Prop)
    (X:Finset V) (Z:Finset U) (x:I↪V) (u:J↪U)
    (hx:∀ i,x i∉X) (hu:∀ j,u j∉Z)
    (hxcover:∀ a∉X,∃ i,x i=a) (hucover:∀ z∉Z,∃ j,u j=z)
    (A:I→Finset V) (B:I→Finset U) (T Y:J→Finset V)
    (hA:∀ i,A i⊆X) (hB:∀ i,B i⊆Z) (hY:∀ j,Y j⊆X)
    (hQr:∀ i a,Q.Adj (x i) a↔a∈A i)
    (hHr:∀ i z,H (x i) z↔z∈B i)
    (hHc:∀ j a,H a (u j)↔a∈Y j)
    (hFroot:∀ i,∀ a∈A i,¬F.Adj (x i) a)
    (D:∀ j,Finset (LocalOrdinaryCycle Q F (T j) 3))
    (hD:∀ j,∀ C∈D j,∀ C'∈D j,C≠C'→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices C'))
    (hDcover:∀ j,(D j).biUnion localOrdinaryVertices=Y j)
    (hDdis:∀ i j,i≠j→Disjoint (localOrdinaryFactorGraph (D i)) (localOrdinaryFactorGraph (D j)))
    (hAB:∀ i,Disjoint ((A i).image Sum.inl) ((B i).image Sum.inr))
    (M:∀ i,Finset (EndpointTriangle (ordinaryPhysicalGraph Q H) (ordinaryPhysicalGraph F (fun _ _=>False))
      ((A i).image Sum.inl) ((B i).image Sum.inr)))
    (hM:∀ i,∀ C∈M i,∀ C'∈M i,C≠C'→Disjoint C.val C'.val)
    (hMcover:∀ i,(M i).biUnion endpointTriangleVertices=(A i).image Sum.inl∪(B i).image Sum.inr)
    (hMdis:∀ i j,i≠j→Disjoint (endpointFactorGraph (hAB i) (M i)) (endpointFactorGraph (hAB j) (M j)))
    (hmixed:∀ j i,Disjoint ((localOrdinaryFactorGraph (D j)).map (Function.Embedding.inl:V↪V⊕U))
      (endpointFactorGraph (hAB i) (M i)))
    (limit:ℝ) (hinnerBound:∀w:V⊕U,
      (((⨆ j,(localOrdinaryFactorGraph (D j)).map (Function.Embedding.inl:V↪V⊕U))⊔
        (⨆ i,endpointFactorGraph (hAB i) (M i))).degree w:ℝ)≤limit):
    ∃ R:SimpleGraph V,∃ S:V→U→Prop,
      R≤Q ∧ (∀ a z,S a z→H a z) ∧ HasOrdinaryWheelDecomposition R S 3 ∧
      (Q\R).support⊆(X:Set V) ∧
      (∀ a z,H a z∧¬S a z→a∈X∧z∈Z) ∧
      spanningRestriction (ordinaryPhysicalGraph R S) (ordinaryInnerVertices X Z)=
        (⨆ j,(localOrdinaryFactorGraph (D j)).map (Function.Embedding.inl:V↪V⊕U))⊔
          (⨆ i,endpointFactorGraph (hAB i) (M i)) ∧
      (∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph R S) (ordinaryInnerVertices X Z)).degree w:ℝ)≤limit):=by
  obtain ⟨R,S,hR,hS,hdec,houtR,houtS,heq⟩:=ordinary_triangle_boundary_finish Q F H X Z x u hx hu hxcover hucover
    A B T Y hA hB hY hQr hHr hHc hFroot D hD hDcover hDdis hAB M hM hMcover hMdis hmixed
  refine ⟨R,S,hR,hS,hdec,houtR,houtS,heq,?_⟩
  intro w
  rw [heq]
  convert hinnerBound w using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
