module

public import Oberwolfach.OrdinaryTriangleSelectedFactors
public import Oberwolfach.OrdinaryTriangleBoundaryFinishWithHost

@[expose] public section
/-! Keep the original host and conflict conditions when the selected
triangle factors complete all boundary incidences. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I J:Type} [Fintype V] [Fintype U] [Fintype I] [Fintype J]
  [DecidableEq V] [DecidableEq U] [DecidableEq I] [DecidableEq J]

theorem ordinary_triangle_finish_from_selected_factors_with_host (Q F:SimpleGraph V) (H:V→U→Prop)
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
      R≤Q ∧ (∀a z,S a z→H a z) ∧
      HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=3)) (ordinaryHostResources R S) ∧
      HasOrdinaryWheelDecomposition R S 3 ∧
      (Q\R).support⊆(X:Set V) ∧
      (∀a z,H a z∧¬S a z→a∈X∧z∈Z) ∧
      (∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph R S) (ordinaryInnerVertices X Z)).degree w:ℝ)≤limit):=by
  obtain ⟨R,S,hR,hS,hhost,hdec,houtR,houtS,heq⟩:=ordinary_triangle_boundary_finish_with_host Q F H X Z x u hx hu hxcover hucover
    A B T Y hA hB hY hQr hHr hHc hFroot C.hub C.hub_disjoint C.hub_cover C.hub_cross hAB
    C.row C.row_disjoint C.row_cover C.row_cross C.mixed_cross
  have hdeg:∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph R S) (ordinaryInnerVertices X Z)).degree w:ℝ)≤limit:=by
    intro w;rw [heq]
    convert C.inner_degree w using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  exact ⟨R,S,hR,hS,hhost,hdec,houtR,houtS,hdeg⟩
end Oberwolfach
