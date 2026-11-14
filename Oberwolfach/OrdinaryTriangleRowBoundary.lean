module

public import Oberwolfach.TypedBoundaryTriangles
public import Oberwolfach.EndpointFactorGraphChoice
public import Oberwolfach.TriangleBoundaryCompletion

@[expose] public section

/-! Complete all selected endpoint-triangle factors at their actual row
roots. Each selected triangle is retained, and the physical inner graph
and every outside-root incidence are identified exactly. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I:Type} [Fintype V] [Fintype U] [Fintype I]
  [DecidableEq V] [DecidableEq U] [DecidableEq I]

theorem endpoint_triangle_graph_eq {W:Type} [Fintype W] [DecidableEq W]
    (P F:SimpleGraph W) (A B:Finset W) (hAB:Disjoint A B) (C:EndpointTriangle P F A B):
    (endpointAsLocalCycle hAB C).val.val.val=spanningRestriction ⊤ C.val:=by
  ext v w
  rw [complete_on_adj]
  have ht:=(endpointAsLocalCycle hAB C).val.val.property.triangle_adj v w
  have hmem (a:W):a∈(endpointAsLocalCycle hAB C).val.val.val.support↔a∈C.val:=by
    rw [←Set.mem_toFinset]
    change a∈localOrdinaryVertices (endpointAsLocalCycle hAB C)↔a∈C.val
    rw [endpointAsLocalCycle_vertices];rfl
  simpa only [hmem] using ht

theorem endpoint_factor_graph_triangles {W:Type} [Fintype W] [DecidableEq W]
    (P F:SimpleGraph W) (A B:Finset W) (hAB:Disjoint A B) (M:Finset (EndpointTriangle P F A B)):
    endpointFactorGraph hAB M=⨆ C:M,spanningRestriction ⊤ C.val.val:=by
  ext v w
  simp only [endpointFactorGraph,localOrdinaryFactorGraph_adj,Finset.mem_image,SimpleGraph.iSup_adj]
  constructor
  · rintro ⟨_,⟨C,hC,rfl⟩,hvw⟩
    exact ⟨⟨C,hC⟩,by rwa [endpoint_triangle_graph_eq] at hvw⟩
  · rintro ⟨C,hC⟩
    exact ⟨endpointAsLocalCycle hAB C.val,⟨C.val,C.property,rfl⟩,by rwa [endpoint_triangle_graph_eq]⟩

theorem ordinary_triangle_row_boundary (Q F:SimpleGraph V) (H:V→U→Prop)
    (X:Finset V) (Z:Finset U) (x:I↪V) (A:I→Finset V) (B:I→Finset U)
    (hx:∀ i,x i∉X) (hA:∀ i,A i⊆X) (hB:∀ i,B i⊆Z)
    (hQ:∀ i,∀ v∈A i,Q.Adj (x i) v) (hH:∀ i,∀ u∈B i,H (x i) u)
    (hF:∀ i,∀ v∈A i,¬F.Adj (x i) v)
    (hAB:∀ i,Disjoint ((A i).image Sum.inl) ((B i).image Sum.inr))
    (M:∀ i,Finset (EndpointTriangle (ordinaryPhysicalGraph Q H) (ordinaryPhysicalGraph F (fun _ _=>False))
      ((A i).image Sum.inl) ((B i).image Sum.inr)))
    (hM:∀ i,∀ C∈M i,∀ D∈M i,C≠D→Disjoint C.val D.val)
    (hcover:∀ i,(M i).biUnion endpointTriangleVertices=(A i).image Sum.inl∪(B i).image Sum.inr)
    (hcross:∀ i j,i≠j→Disjoint (endpointFactorGraph (hAB i) (M i)) (endpointFactorGraph (hAB j) (M j))):
    ∃ W:(Σ i,M i)→OrdinaryWheel Q F H 3,
      (∀ j,ordinaryWheelPhysicalGraph (W j)=spanningRestriction ⊤ (insert (Sum.inl (x j.1)) j.2.val.val)) ∧
      (∀ i j,i≠j→Disjoint (ordinaryWheelResources (W i)) (ordinaryWheelResources (W j))) ∧
      HasOrdinaryWheelDecomposition (wheelFamilyRim W) (wheelFamilySpokes W) 3 ∧
      spanningRestriction (⨆ j,ordinaryWheelPhysicalGraph (W j)) (X.image Sum.inl∪Z.image Sum.inr)=
        ⨆ i,endpointFactorGraph (hAB i) (M i) ∧
      (∀ z∉X.image Sum.inl∪Z.image Sum.inr,∀ v,
        (⨆ j,ordinaryWheelPhysicalGraph (W j)).Adj z v↔
          ∃ i,Sum.inl (x i)=z∧v∈(A i).image Sum.inl∪(B i).image Sum.inr):=by
  let Ω:=X.image Sum.inl∪Z.image Sum.inr
  let root:(Σ i,M i)→V⊕U:=fun j=>Sum.inl (x j.1)
  let T:(Σ i,M i)→Finset (V⊕U):=fun j=>j.2.val.val
  have hex (j:Σ i,M i):∃ W:OrdinaryWheel Q F H 3,
      ordinaryWheelPhysicalGraph W=spanningRestriction ⊤ (insert (root j) (T j)):=by
    obtain ⟨W,hW,_⟩:=endpoint_triangle_complete_at_row Q F H (A j.1) (B j.1) (x j.1)
      (fun h=>hx j.1 (hA j.1 h)) (hQ j.1) (hH j.1) (hF j.1) j.2.val
    exact ⟨W,hW⟩
  choose W hW using hex
  have hroot (j:Σ i,M i):root j∉Ω:=by
    simpa only [root,Ω,Finset.mem_union,Finset.mem_image,Sum.inl.injEq,Sum.inr_ne_inl,
      and_false,exists_false,or_false,exists_eq_right] using hx j.1
  have hT (j:Σ i,M i):T j⊆Ω:=by
    intro a ha
    rcases Finset.mem_union.mp (j.2.val.property.1 ha) with ha|ha
    · obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp ha
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v,hA j.1 hv,rfl⟩)
    · obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp ha
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨u,hB j.1 hu,rfl⟩)
  have hinnerle (j:Σ i,M i):spanningRestriction (⊤:SimpleGraph (V⊕U)) (T j)≤
      endpointFactorGraph (hAB j.1) (M j.1):=by
    rw [endpoint_factor_graph_triangles]
    exact le_iSup (fun C:M j.1=>spanningRestriction ⊤ C.val.val) j.2
  have hsame (i j:Σ k,M k) (hne:i≠j) (he:root i=root j):Disjoint (T i) (T j):=by
    have hij:i.1=j.1:=x.injective (Sum.inl.inj he)
    rcases i with ⟨i,C⟩;rcases j with ⟨j,D⟩
    dsimp only at hij;subst j
    exact hM i C.val C.property D.val D.property (fun hc=>hne (congrArg (Sigma.mk i) (Subtype.ext hc)))
  have hinner (i j:Σ k,M k) (hne:i≠j):Disjoint (spanningRestriction (⊤:SimpleGraph (V⊕U)) (T i))
      (spanningRestriction ⊤ (T j)):=by
    by_cases hij:i.1=j.1
    · have hd:=hsame i j hne (by change Sum.inl (x i.1)=Sum.inl (x j.1);rw [hij])
      apply disjoint_iff_inf_le.mpr
      intro a b hab
      exact (Finset.disjoint_left.mp hd ((complete_on_adj (T i) a b).mp hab.1).1
        ((complete_on_adj (T j) a b).mp hab.2).1).elim
    · exact (hcross i.1 j.1 hij).mono (hinnerle i) (hinnerle j)
  have hdis (i j:Σ k,M k) (hne:i≠j):Disjoint (ordinaryWheelResources (W i)) (ordinaryWheelResources (W j)):=by
    have hg:Disjoint (ordinaryWheelPhysicalGraph (W i)) (ordinaryWheelPhysicalGraph (W j)):=by
      rw [hW i,hW j]
      exact root_completed_cliques_disjoint Ω (T i) (T j) (root i) (root j)
        (hT i) (hT j) (hroot i) (hroot j) (hinner i j hne) (hsame i j hne)
    have he:=SimpleGraph.disjoint_edgeFinset.mpr hg
    rw [ordinaryWheelPhysicalGraph_edges,ordinaryWheelPhysicalGraph_edges] at he
    exact Finset.disjoint_left.mpr (fun e hei hej=>Finset.disjoint_left.mp he
      (Finset.mem_image.mpr ⟨e,hei,rfl⟩) (Finset.mem_image.mpr ⟨e,hej,rfl⟩))
  have hgraphs:(⨆ j,ordinaryWheelPhysicalGraph (W j))=
      ⨆ j,spanningRestriction (⊤:SimpleGraph (V⊕U)) (insert (root j) (T j)):=iSup_congr hW
  refine ⟨W,hW,hdis,wheelFamily_decomposition W hdis,?_,?_⟩
  · rw [hgraphs,root_completed_cliques_inner Ω root T hroot hT]
    ext a b
    simp only [SimpleGraph.iSup_adj]
    constructor
    · rintro ⟨j,hj⟩;exact ⟨j.1,hinnerle j hj⟩
    · rintro ⟨i,hi⟩
      rw [endpoint_factor_graph_triangles] at hi
      obtain ⟨C,hC⟩:=SimpleGraph.iSup_adj.mp hi
      exact ⟨⟨i,C⟩,hC⟩
  · intro z hz v
    rw [hgraphs,root_completed_cliques_at_root Ω root T hroot hT z v hz]
    constructor
    · rintro ⟨j,hj,hv⟩
      refine ⟨j.1,hj,?_⟩
      rw [←hcover j.1]
      exact Finset.mem_biUnion.mpr ⟨j.2.val,j.2.property,hv⟩
    · rintro ⟨i,hi,hv⟩
      rw [←hcover i] at hv
      obtain ⟨C,hC,hv⟩:=Finset.mem_biUnion.mp hv
      exact ⟨⟨i,⟨C,hC⟩⟩,hi,hv⟩

end Oberwolfach
