module

public import Oberwolfach.InducedDomainCounts
public import Oberwolfach.EndpointTriangleFactor

@[expose] public section

/-! Endpoint triangles and their fixed weights are transported through an
injective vertex map. Every supported triangle is retained exactly once. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

def endpointTriangleLift (e:W↪V) (Q F:SimpleGraph V) (S T:Finset V)
    (C:EndpointTriangle (Q.comap e) (F.comap e) (embeddingPullFinset e S) (embeddingPullFinset e T)) :
    EndpointTriangle Q F S T := by
  refine ⟨C.val.image e,?_,?_,?_,?_,?_⟩
  · rintro v hv
    obtain ⟨w,hw,rfl⟩:=Finset.mem_image.mp hv
    simpa only [Finset.mem_union,embeddingPullFinset_mem] using C.property.1 hw
  · have he:(C.val.image e)∩S=(C.val∩embeddingPullFinset e S).image e:=by
      ext v;simp only [Finset.mem_inter,Finset.mem_image,embeddingPullFinset_mem]
      constructor
      · rintro ⟨⟨w,hw,rfl⟩,hs⟩;exact ⟨w,⟨hw,hs⟩,rfl⟩
      · rintro ⟨w,⟨hw,hs⟩,rfl⟩;exact ⟨⟨w,hw,rfl⟩,hs⟩
    rw [he,Finset.card_image_of_injective _ e.injective]
    exact C.property.2.1
  · have he:(C.val.image e)∩T=(C.val∩embeddingPullFinset e T).image e:=by
      ext v;simp only [Finset.mem_inter,Finset.mem_image,embeddingPullFinset_mem]
      constructor
      · rintro ⟨⟨w,hw,rfl⟩,ht⟩;exact ⟨w,⟨hw,ht⟩,rfl⟩
      · rintro ⟨w,⟨hw,ht⟩,rfl⟩;exact ⟨⟨w,hw,rfl⟩,ht⟩
    rw [he,Finset.card_image_of_injective _ e.injective]
    exact C.property.2.2.1
  · rintro v hv w hw hne
    obtain ⟨v',hv',rfl⟩:=Finset.mem_image.mp hv
    obtain ⟨w',hw',rfl⟩:=Finset.mem_image.mp hw
    exact C.property.2.2.2.1 v' hv' w' hw' (fun he=>hne (congrArg e he))
  · rintro v hv w hw
    obtain ⟨v',hv',rfl⟩:=Finset.mem_image.mp hv
    obtain ⟨w',hw',rfl⟩:=Finset.mem_image.mp hw
    exact C.property.2.2.2.2 v' hv' w' hw'

@[simp] theorem endpointTriangleLift_vertices (e:W↪V) (Q F:SimpleGraph V) (S T:Finset V)
    (C:EndpointTriangle (Q.comap e) (F.comap e) (embeddingPullFinset e S) (embeddingPullFinset e T)) :
    (endpointTriangleLift e Q F S T C).val=C.val.image e := rfl

theorem endpointTriangleLift_bijective (e:W↪V) (Q F:SimpleGraph V) (S T:Finset V)
    (hS:∀ v∈S,∃ w,e w=v) (hT:∀ v∈T,∃ w,e w=v) :
    Function.Bijective (endpointTriangleLift e Q F S T) := by
  constructor
  · intro C D h
    apply Subtype.ext
    have hh:=congrArg Subtype.val h
    change C.val.image e=D.val.image e at hh
    have hi:=congrArg (embeddingPullFinset e) hh
    simpa using hi
  · intro C
    have hsupp:∀ v∈C.val,∃ w,e w=v:=by
      intro v hv
      exact (Finset.mem_union.mp (C.property.1 hv)).elim (hS v) (hT v)
    let X:=embeddingPullFinset e C.val
    have hXS:X∩embeddingPullFinset e S=embeddingPullFinset e (C.val∩S):=by
      ext v;simp [X]
    have hXT:X∩embeddingPullFinset e T=embeddingPullFinset e (C.val∩T):=by
      ext v;simp [X]
    let hX:EndpointTriangle (Q.comap e) (F.comap e) (embeddingPullFinset e S) (embeddingPullFinset e T):=by
      refine ⟨X,?_,?_,?_,?_,?_⟩
      · intro w hw
        simpa only [Finset.mem_union,embeddingPullFinset_mem] using
          C.property.1 ((embeddingPullFinset_mem _ _ _).mp hw)
      · rw [hXS,embeddingPullFinset_card e (C.val∩S) (fun v hv=>hS v (Finset.mem_inter.mp hv).2)]
        exact C.property.2.1
      · rw [hXT,embeddingPullFinset_card e (C.val∩T) (fun v hv=>hT v (Finset.mem_inter.mp hv).2)]
        exact C.property.2.2.1
      · intro v hv w hw hne
        exact C.property.2.2.2.1 (e v) ((embeddingPullFinset_mem _ _ _).mp hv)
          (e w) ((embeddingPullFinset_mem _ _ _).mp hw) (e.injective.ne hne)
      · intro v hv w hw
        exact C.property.2.2.2.2 (e v) ((embeddingPullFinset_mem _ _ _).mp hv)
          (e w) ((embeddingPullFinset_mem _ _ _).mp hw)
    refine ⟨hX,Subtype.ext ?_⟩
    exact embeddingPullFinset_image e C.val hsupp

noncomputable def endpointTriangleEquiv (e:W↪V) (Q F:SimpleGraph V) (S T:Finset V)
    (hS:∀ v∈S,∃ w,e w=v) (hT:∀ v∈T,∃ w,e w=v) :
    EndpointTriangle (Q.comap e) (F.comap e) (embeddingPullFinset e S) (embeddingPullFinset e T) ≃
      EndpointTriangle Q F S T :=
  Equiv.ofBijective _ (endpointTriangleLift_bijective e Q F S T hS hT)

theorem endpointTriangleLift_weighted_degree (e:W↪V) (Q F:SimpleGraph V) (S T:Finset V)
    (hS:∀ v∈S,∃ w,e w=v) (hT:∀ v∈T,∃ w,e w=v)
    (wt:EndpointTriangle Q F S T→ℝ) (v:W) :
    hypergraphWeightedDegree endpointTriangleVertices (fun C=>wt (endpointTriangleLift e Q F S T C)) v=
      hypergraphWeightedDegree endpointTriangleVertices wt (e v) := by
  let E:=endpointTriangleEquiv e Q F S T hS hT
  have hh:=Equiv.sum_comp E (fun C=>if e v∈endpointTriangleVertices C then wt C else 0)
  unfold hypergraphWeightedDegree
  convert hh using 1
  apply Finset.sum_congr rfl
  intro C _
  have he:(e v∈endpointTriangleVertices (E C)) ↔ v∈endpointTriangleVertices C:=by
    change (e v∈C.val.image e) ↔ v∈C.val
    simp [e.injective.eq_iff]
  simp only [he]
  rfl

theorem endpointTriangleLift_decomposition (e:W↪V) (Q F:SimpleGraph V) (S T:Finset V)
    (hS:∀ v∈S,∃ w,e w=v) (hT:∀ v∈T,∃ w,e w=v)
    (hd:HasResourceDecomposition (endpointTriangleVertices (Q:=Q.comap e) (F:=F.comap e)
      (S:=embeddingPullFinset e S) (T:=embeddingPullFinset e T))
      (embeddingPullFinset e S∪embeddingPullFinset e T)) :
    HasResourceDecomposition (endpointTriangleVertices (Q:=Q) (F:=F) (S:=S) (T:=T)) (S∪T) := by
  obtain ⟨M,hM,hcover⟩:=hd
  refine ⟨M.image (endpointTriangleLift e Q F S T),?_,?_⟩
  · intro C hC D hD hne
    obtain ⟨C',hC',rfl⟩:=Finset.mem_image.mp hC
    obtain ⟨D',hD',rfl⟩:=Finset.mem_image.mp hD
    change Disjoint (C'.val.image e) (D'.val.image e)
    apply Finset.disjoint_left.mpr
    intro v hv hw
    obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hv
    obtain ⟨b,hb,he⟩:=Finset.mem_image.mp hw
    have he':b=a:=e.injective he
    subst b
    exact Finset.disjoint_left.mp (hM C' hC' D' hD' (fun he=>hne (congrArg _ he))) ha hb
  · have hi:=congrArg (fun A:Finset W=>A.image e) hcover
    rw [Finset.image_union,embeddingPullFinset_image e S hS,embeddingPullFinset_image e T hT] at hi
    apply Eq.trans _ hi
    rw [Finset.biUnion_image,Finset.image_biUnion]
    rfl

end Oberwolfach
