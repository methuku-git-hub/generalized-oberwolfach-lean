module

public import Oberwolfach.RestrictedResourceSubsetCounts
public import Oberwolfach.BernoulliVertexSampling

@[expose] public section
/-! Restricting a fixed resource set to the sampled ground set preserves
exactly its actual sampled cardinality. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem sampled_resource_subset_card_filter (state:V→Bool) (S:Finset V):
    let e:{v:V // v∈bernoulliVertexSet state}↪V:=Function.Embedding.subtype _
    (restrictedResourceSubset e S).card=(S.filter (fun v=>state v=true)).card:=by
  intro e
  have himage:(restrictedResourceSubset e S).image e=S.filter (fun v=>state v=true):=by
    ext x
    constructor
    · intro hx
      obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hx
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hv).2,(mem_bernoulliVertexSet state v.val).mp v.property⟩
    · intro hx
      obtain ⟨hxS,hxstate⟩:=Finset.mem_filter.mp hx
      let v:{v:V // v∈bernoulliVertexSet state}:=⟨x,(mem_bernoulliVertexSet state x).mpr hxstate⟩
      exact Finset.mem_image.mpr ⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxS⟩,rfl⟩
  rw [←himage,Finset.card_image_of_injective _ e.injective]
end Oberwolfach
