module

public import Oberwolfach.RestrictedResourceNestedLift

@[expose] public section
/-! Lift a matching from a surviving resource set to its fixed parent sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V C:Type} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]

def survivingResourceEmbedding (S T:Finset V) (hST:S⊆T):S↪T where
  toFun x:=⟨x.val,hST x.property⟩
  inj' :=by intro a b h;apply Subtype.ext;exact congrArg (fun z:T=>z.val) h

def survivingCandidateEmbedding (R:C→Finset V) (S T:Finset V) (hST:S⊆T):
    RestrictedResource R (Function.Embedding.subtype (·∈S))↪
      RestrictedResource R (Function.Embedding.subtype (·∈T)):=
  restrictedResourceNestedLift R (Function.Embedding.subtype (·∈S))
    (Function.Embedding.subtype (·∈T)) (survivingResourceEmbedding S T hST) (fun _=>rfl)

theorem surviving_candidate_original_id (R:C→Finset V) (S T:Finset V) (hST:S⊆T)
    (a:RestrictedResource R (Function.Embedding.subtype (·∈S))):
    (survivingCandidateEmbedding R S T hST a).val=a.val :=rfl

theorem surviving_candidate_matching_lift (R:C→Finset V) (S T:Finset V) (hST:S⊆T)
    (M:Finset (RestrictedResource R (Function.Embedding.subtype (·∈S))))
    (hM:∀a∈M,∀b∈M,a≠b→Disjoint (restrictedResourceSet R (Function.Embedding.subtype (·∈S)) a)
      (restrictedResourceSet R (Function.Embedding.subtype (·∈S)) b)):
    ∀a∈M.map (survivingCandidateEmbedding R S T hST),
      ∀b∈M.map (survivingCandidateEmbedding R S T hST),a≠b→
        Disjoint (restrictedResourceSet R (Function.Embedding.subtype (·∈T)) a)
          (restrictedResourceSet R (Function.Embedding.subtype (·∈T)) b) :=by
  exact restricted_resource_nested_lift_matching R _ _ (survivingResourceEmbedding S T hST) (fun _=>rfl) M hM

theorem surviving_candidate_count_lift (R:C→Finset V) (S T:Finset V) (hST:S⊆T)
    (M:Finset (RestrictedResource R (Function.Embedding.subtype (·∈S)))) (p:C→Prop) [DecidablePred p]:
    ((M.map (survivingCandidateEmbedding R S T hST)).filter (fun c=>p c.val)).card =
      (M.filter (fun c=>p c.val)).card :=by
  exact restricted_resource_nested_lift_count R _ _ (survivingResourceEmbedding S T hST) (fun _=>rfl) M p

theorem surviving_candidate_positive_weight_lift (R:C→Finset V) (S T:Finset V) (hST:S⊆T)
    (M:Finset (RestrictedResource R (Function.Embedding.subtype (·∈S)))) (w:C→ℝ)
    (hpos:∀a∈M,0<w a.val):
    ∀a∈M.map (survivingCandidateEmbedding R S T hST),0<w a.val :=by
  intro a ha
  obtain ⟨b,hb,h⟩:=Finset.mem_map.mp ha
  rw [←h]
  exact hpos b hb
end Oberwolfach
