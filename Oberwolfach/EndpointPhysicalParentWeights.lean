module

public import Oberwolfach.EndpointParentWeightFamily
public import Oberwolfach.OrdinaryEndpointEligibleGeometry

@[expose] public section
/-! Choose all physical parent matching weights before sampling, directly
from the original rim-domain three-quarter degree condition. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

structure EndpointPhysicalParentWeights (P:SimpleGraph V) (A X:Finset V)
    (weight:V→Sym2 (V⊕U)→ℝ):Prop where
  bounded:∀x∈X,∀v∈(A.image Sum.inl)∩(ordinaryPhysicalGraph P (fun _ _=>False)).neighborFinset (Sum.inl x),
    ∀w∈(A.image Sum.inl)∩(ordinaryPhysicalGraph P (fun _ _=>False)).neighborFinset (Sum.inl x),
      0≤weight x s(v,w)∧weight x s(v,w)≤40/A.card
  mass:∀x∈X,∀v∈(A.image Sum.inl)∩(ordinaryPhysicalGraph P (fun _ _=>False)).neighborFinset (Sum.inl x),
    ∑w∈(A.image Sum.inl)∩(ordinaryPhysicalGraph P (fun _ _=>False)).neighborFinset (Sum.inl x),weight x s(v,w)=1
  zero:∀x∈X,∀v w,¬(ordinaryPhysicalGraph P (fun _ _=>False)).Adj v w→weight x s(v,w)=0
  positive:∀x∈X,∀F:SimpleGraph (V⊕U),∀e∈(endpointEligibleGraph (ordinaryPhysicalGraph P (fun _ _=>False)) F
    ((A.image Sum.inl)∩(ordinaryPhysicalGraph P (fun _ _=>False)).neighborFinset (Sum.inl x)) (Sum.inl x)).edgeSet,
    (1/30:ℝ)/A.card≤weight x e∧weight x e≤40/A.card

theorem endpoint_physical_parent_weight_family (P:SimpleGraph V) (A X:Finset V) (hn:32≤A.card)
    (hdeg:∀x∈X,∀v∈insert x A,(3/4:ℝ)*A.card≤((A∩P.neighborFinset v).card:ℝ)):
    ∃weight:V→Sym2 (V⊕U)→ℝ,EndpointPhysicalParentWeights P A X weight:=by
  let f:V↪V⊕U:=Function.Embedding.inl
  let Pphys:SimpleGraph (V⊕U):=ordinaryPhysicalGraph P (fun _ _=>False)
  have hcard:(A.image f).card=A.card:=Finset.card_image_of_injective _ f.injective
  have hbig:32≤(A.image f).card:=by simpa [hcard] using hn
  have hd:∀y∈X.image f,∀z∈insert y (A.image f),
      (3/4:ℝ)*(A.image f).card≤(((A.image f)∩Pphys.neighborFinset z).card:ℝ):=by
    intro y hy z hz
    obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hy
    have hz':∃v∈insert x A,f v=z:=by
      rcases Finset.mem_insert.mp hz with h|h
      · exact ⟨x,Finset.mem_insert_self _ _,h.symm⟩
      · obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp h
        exact ⟨v,Finset.mem_insert_of_mem hv,rfl⟩
    obtain ⟨v,hv,rfl⟩:=hz'
    have he:(A.image f)∩Pphys.neighborFinset (f v)=(A∩P.neighborFinset v).image f:=by
      exact ordinary_endpoint_parent_neighbors P A v
    rw [hcard,he,Finset.card_image_of_injective _ f.injective]
    exact hdeg x hx v hv
  obtain ⟨w,hw⟩:=endpoint_parent_weight_family Pphys (A.image f) (X.image f) hbig hd
  refine ⟨fun x=>w (f x),?_⟩
  constructor
  · intro x hx v hv z hz
    have hh:=(hw (f x) (Finset.mem_image.mpr ⟨x,hx,rfl⟩)).1 v hv z hz
    simpa only [hcard] using hh
  · intro x hx v hv
    exact (hw (f x) (Finset.mem_image.mpr ⟨x,hx,rfl⟩)).2.1 v hv
  · intro x hx v z h
    exact (hw (f x) (Finset.mem_image.mpr ⟨x,hx,rfl⟩)).2.2.1 v z h
  · intro x hx F e he
    have hh:=(hw (f x) (Finset.mem_image.mpr ⟨x,hx,rfl⟩)).2.2.2 F e he
    simpa only [hcard] using hh
end Oberwolfach
