module

public import Oberwolfach.RestrictedResourceStateLift

@[expose] public section
/-! The surviving candidate type contains exactly the parent candidates whose
original resource sets are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V C:Type} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]

theorem surviving_candidate_lift_range_iff
    (R:C→Finset V) (S T:Finset V) (hST:S⊆T)
    (a:RestrictedResource R (Function.Embedding.subtype (·∈T))):
    (∃b:RestrictedResource R (Function.Embedding.subtype (·∈S)),
      survivingCandidateEmbedding R S T hST b=a) ↔ R a.val ⊆ S :=by
  constructor
  · rintro ⟨b,rfl⟩ z hz
    obtain ⟨v,hv⟩:=b.property z hz
    rw [←hv]
    exact v.property
  · intro ha
    let b:RestrictedResource R (Function.Embedding.subtype (·∈S)):=
      ⟨a.val,fun z hz=>⟨⟨z,ha hz⟩,rfl⟩⟩
    refine ⟨b,?_⟩
    apply Subtype.ext
    rfl
end Oberwolfach
