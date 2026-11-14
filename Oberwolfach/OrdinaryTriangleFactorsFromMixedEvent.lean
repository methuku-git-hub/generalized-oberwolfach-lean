module

public import Oberwolfach.OrdinaryTriangleSelectedFactors
public import Oberwolfach.MixedFreshBoundaryFactors

@[expose] public section
/-! The existing mixed fresh-factor event supplies exactly the selected
triangle-factor record used by the canonical boundary finish. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I J:Type} [Fintype V] [Fintype U] [Fintype I] [Fintype J]
  [DecidableEq V] [DecidableEq U] [DecidableEq I] [DecidableEq J]

theorem ordinary_triangle_selected_factors_from_mixed
    (Q F:SimpleGraph V) (H:V→U→Prop) (A:I→Finset V) (B:I→Finset U) (T Y:J→Finset V)
    (hAB:∀i,Disjoint ((A i).image Sum.inl) ((B i).image Sum.inr))
    (D:∀j,Finset (LocalOrdinaryCycle Q F (T j) 3))
    (M:∀i,Finset (EndpointTriangle (ordinaryPhysicalGraph Q H) (ordinaryPhysicalGraph F (fun _ _=>False))
      ((A i).image Sum.inl) ((B i).image Sum.inr)))
    (hD:∀j,(∀C∈D j,∀C'∈D j,C≠C'→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices C')) ∧
      (D j).biUnion localOrdinaryVertices=Y j)
    (hM:∀i,(∀C∈M i,∀C'∈M i,C≠C'→Disjoint (endpointTriangleVertices C) (endpointTriangleVertices C')) ∧
      (M i).biUnion endpointTriangleVertices=(A i).image Sum.inl∪(B i).image Sum.inr)
    (hdis:∀a b:J⊕I,a≠b→Disjoint
      (Sum.elim (fun j=>(localOrdinaryFactorGraph (D j)).map (Function.Embedding.inl:V↪V⊕U))
        (fun i=>endpointFactorGraph (hAB i) (M i)) a)
      (Sum.elim (fun j=>(localOrdinaryFactorGraph (D j)).map (Function.Embedding.inl:V↪V⊕U))
        (fun i=>endpointFactorGraph (hAB i) (M i)) b))
    (limit:ℝ) (hdeg:∀w:V⊕U,
      ((⨆k:J⊕I,Sum.elim (fun j=>(localOrdinaryFactorGraph (D j)).map (Function.Embedding.inl:V↪V⊕U))
        (fun i=>endpointFactorGraph (hAB i) (M i)) k).degree w:ℝ)≤limit):
    Nonempty (OrdinaryTriangleSelectedFactors Q F H A B T Y hAB limit):=by
  refine ⟨⟨D,fun j=>(hD j).1,fun j=>(hD j).2,?_,M,?_,fun i=>(hM i).2,?_,?_,?_⟩⟩
  · intro i j hij
    have hd:=hdis (Sum.inl i) (Sum.inl j) (by simpa using hij)
    simp only [Sum.elim_inl] at hd
    rw [graph_map_inl_physical,graph_map_inl_physical] at hd
    apply disjoint_iff_inf_le.mpr
    intro a b hab
    exact (disjoint_iff_inf_le.mp hd) (v:=Sum.inl a) (w:=Sum.inl b) ⟨hab.1,hab.2⟩
  · intro i C hC C' hC' hne
    have hh:Disjoint (endpointTriangleVertices C) (endpointTriangleVertices C'):=(hM i).1 C hC C' hC' hne
    exact hh
  · intro i j hij
    have hd:=hdis (Sum.inr i) (Sum.inr j) (by simpa using hij)
    simpa only [Sum.elim_inr] using hd
  · intro j i
    have hd:=hdis (Sum.inl j) (Sum.inr i) Sum.inl_ne_inr
    simpa only [Sum.elim_inl,Sum.elim_inr] using hd
  · intro w
    have hsub:((⨆j,(localOrdinaryFactorGraph (D j)).map (Function.Embedding.inl:V↪V⊕U))⊔
        (⨆i,endpointFactorGraph (hAB i) (M i)))≤
        ⨆k:J⊕I,Sum.elim (fun j=>(localOrdinaryFactorGraph (D j)).map (Function.Embedding.inl:V↪V⊕U))
          (fun i=>endpointFactorGraph (hAB i) (M i)) k:=by
      apply sup_le
      · apply iSup_le;intro j
        exact le_iSup (fun k:J⊕I=>Sum.elim (fun j=>(localOrdinaryFactorGraph (D j)).map (Function.Embedding.inl:V↪V⊕U))
          (fun i=>endpointFactorGraph (hAB i) (M i)) k) (Sum.inl j)
      · apply iSup_le;intro i
        exact le_iSup (fun k:J⊕I=>Sum.elim (fun j=>(localOrdinaryFactorGraph (D j)).map (Function.Embedding.inl:V↪V⊕U))
          (fun i=>endpointFactorGraph (hAB i) (M i)) k) (Sum.inr i)
    have hd:(((⨆j,(localOrdinaryFactorGraph (D j)).map (Function.Embedding.inl:V↪V⊕U))⊔
        (⨆i,endpointFactorGraph (hAB i) (M i))).degree w:ℝ)≤
        ((⨆k:J⊕I,Sum.elim (fun j=>(localOrdinaryFactorGraph (D j)).map (Function.Embedding.inl:V↪V⊕U))
          (fun i=>endpointFactorGraph (hAB i) (M i)) k).degree w:ℝ):=by
      exact_mod_cast (SimpleGraph.degree_le_of_le hsub (v:=w))
    exact hd.trans (hdeg w)
end Oberwolfach
