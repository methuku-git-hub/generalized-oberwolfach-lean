module

public import Oberwolfach.RestrictedResourceStateLift

@[expose] public section
/-! The union of the resources of a matching survives the canonical lift
without adding or removing any resource. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V C:Type} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]

theorem surviving_candidate_covered_resources_lift
    (R:C→Finset V) (S T:Finset V) (hST:S⊆T)
    (M:Finset (RestrictedResource R (Function.Embedding.subtype (·∈S)))):
    let f:=survivingResourceEmbedding S T hST
    let q:=survivingCandidateEmbedding R S T hST
    (M.map q).biUnion (restrictedResourceSet R (Function.Embedding.subtype (·∈T))) =
      (M.biUnion (restrictedResourceSet R (Function.Embedding.subtype (·∈S)))).map f :=by
  intro f q
  ext z
  simp only [Finset.mem_biUnion,Finset.mem_map]
  constructor
  · rintro ⟨b,⟨a,ha,rfl⟩,hz⟩
    have hset:restrictedResourceSet R (Function.Embedding.subtype (·∈T)) (q a)=
        (restrictedResourceSet R (Function.Embedding.subtype (·∈S)) a).map f :=by
      exact restricted_resource_nested_lift_set R _ _ f (fun _=>rfl) a
    rw [hset] at hz
    obtain ⟨w,hw,hwz⟩:=Finset.mem_map.mp hz
    exact ⟨w,⟨a,ha,hw⟩,hwz⟩
  · rintro ⟨w,⟨a,ha,hw⟩,rfl⟩
    refine ⟨q a,⟨a,ha,rfl⟩,?_⟩
    have hset:restrictedResourceSet R (Function.Embedding.subtype (·∈T)) (q a)=
        (restrictedResourceSet R (Function.Embedding.subtype (·∈S)) a).map f :=by
      exact restricted_resource_nested_lift_set R _ _ f (fun _=>rfl) a
    rw [hset]
    exact Finset.mem_map.mpr ⟨w,hw,rfl⟩
end Oberwolfach
