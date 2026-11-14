module

public import Oberwolfach.OrdinaryTriangleInnerFactorsAvoidDeep
public import Oberwolfach.OrdinaryRootFirstDeepFinishData

@[expose] public section
/-! The selected triangle factors on the actual cleaned host give the
root-first finish while protecting the deeper pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I J:Type} [Fintype V] [Fintype U] [Fintype I] [Fintype J]
  [DecidableEq V] [DecidableEq U] [DecidableEq I] [DecidableEq J]

theorem ordinary_triangle_root_first_finish_from_factors
    (Q F:SimpleGraph V) (H:V→U→Prop) (X Tdeep:Finset V) (Z Wdeep:Finset U)
    (η ell t ν:ℝ) (Droot:OrdinaryRootCoverData Q F H X Tdeep Z Wdeep 3 η ell)
    (σ:Sym2 (V⊕U)→Bool) (O:OrdinaryRootFirstCleanupOutcome Q F H X Tdeep Z Wdeep 3 η ell t ν Droot σ)
    (hTX:Tdeep⊆X) (hWZ:Wdeep⊆Z) (x:I↪V) (u:J↪U)
    (hx:∀i,x i∉X) (hu:∀j,u j∉Z)
    (hxcover:∀a∉X,∃i,x i=a) (hucover:∀z∉Z,∃j,u j=z)
    (A:I→Finset V) (B:I→Finset U) (T Y:J→Finset V)
    (hA:∀i,A i⊆X) (hB:∀i,B i⊆Z) (hY:∀j,Y j⊆X)
    (hAB:∀i,Disjoint ((A i).image Sum.inl) ((B i).image Sum.inr)) (limit:ℝ):
    let Q₂:=ordinaryRootFirstCleanRemainderRim Q F H X Tdeep Z Wdeep 3 η ell t ν Droot σ O;
    let H₂:=ordinaryRootFirstCleanRemainderSpokes Q F H X Tdeep Z Wdeep 3 η ell t ν Droot σ O;
    (∀i a,Q₂.Adj (x i) a↔a∈A i)→(∀i z,H₂ (x i) z↔z∈B i)→
    (∀j a,H₂ a (u j)↔a∈Y j)→(∀i,∀a∈A i,¬F.Adj (x i) a)→
    ∀C:OrdinaryTriangleSelectedFactors Q₂ F H₂ A B T Y hAB limit,
    (∀j,Disjoint ((localOrdinaryFactorGraph (C.hub j)).map (Function.Embedding.inl:V↪V⊕U))
      (ordinaryDeepBlocker Tdeep Wdeep))→
    (∀i,Disjoint (endpointFactorGraph (hAB i) (C.row i)) (ordinaryDeepBlocker Tdeep Wdeep))→
    Nonempty (OrdinaryRootFirstDeepFinishData Q F H X Tdeep Z Wdeep 3 η ell t ν Droot σ O limit):=by
  intro Q₂ H₂ hQr hHr hHc hFroot C hhub hrow
  obtain ⟨R,S,hR,hS,hhost,hdec,hRsupport,hSsupport,heq⟩:=ordinary_triangle_boundary_finish_with_host
    Q₂ F H₂ X Z x u hx hu hxcover hucover A B T Y hA hB hY hQr hHr hHc hFroot
    C.hub C.hub_disjoint C.hub_cover C.hub_cross hAB C.row C.row_disjoint C.row_cover C.row_cross C.mixed_cross
  have hcost:∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph R S) (ordinaryInnerVertices X Z)).degree w:ℝ)≤limit:=by
    intro w;rw [heq]
    convert C.inner_degree w using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hdeep:=ordinary_triangle_inner_factors_avoid_deep R S X Tdeep Z Wdeep hTX hWZ
    (fun j=>(localOrdinaryFactorGraph (C.hub j)).map (Function.Embedding.inl:V↪V⊕U))
    (fun i=>endpointFactorGraph (hAB i) (C.row i)) heq hhub hrow
  exact ⟨⟨R,S,hR,hS,hhost,hdec,hRsupport,hSsupport,hcost,hdeep⟩⟩
end Oberwolfach
