module

public import Oberwolfach.RestrictedResourceStateLift

@[expose] public section
/-! Equal resource sets give an identity-on-candidates equivalence, preserving
matching tests and the full fixed-weight test mass. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V C:Type} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]

def equalStateCandidateEquiv (R:C→Finset V) (S T:Finset V) (h:S=T):
    RestrictedResource R (Function.Embedding.subtype (·∈S)) ≃
      RestrictedResource R (Function.Embedding.subtype (·∈T)) :=by
  subst T
  exact Equiv.refl _

theorem equal_state_candidate_equiv_val (R:C→Finset V) (S T:Finset V) (h:S=T)
    (a:RestrictedResource R (Function.Embedding.subtype (·∈S))):
    (equalStateCandidateEquiv R S T h a).val=a.val :=by
  subst T
  rfl

theorem equal_state_full_weighted_test_mass (R:C→Finset V) (S T:Finset V) (h:S=T) (test:C→ℝ):
    (∑a:RestrictedResource R (Function.Embedding.subtype (·∈T)),test a.val)=
      ∑a:RestrictedResource R (Function.Embedding.subtype (·∈S)),test a.val :=by
  subst T
  rfl

theorem equal_state_selected_weighted_test_sum (R:C→Finset V) (S T:Finset V) (h:S=T)
    (M:Finset (RestrictedResource R (Function.Embedding.subtype (·∈S)))) (test:C→ℝ):
    (∑a∈M.map (equalStateCandidateEquiv R S T h).toEmbedding,test a.val)=
      ∑a∈M,test a.val :=by
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro a _
  change test ((equalStateCandidateEquiv R S T h a).val)=test a.val
  rw [equal_state_candidate_equiv_val]
theorem equal_state_candidate_matching (R:C→Finset V) (S T:Finset V) (h:S=T)
    (M:Finset (RestrictedResource R (Function.Embedding.subtype (·∈S))))
    (hM:∀a∈M,∀b∈M,a≠b→Disjoint
      (restrictedResourceSet R (Function.Embedding.subtype (·∈S)) a)
      (restrictedResourceSet R (Function.Embedding.subtype (·∈S)) b)):
    ∀a∈M.map (equalStateCandidateEquiv R S T h).toEmbedding,
      ∀b∈M.map (equalStateCandidateEquiv R S T h).toEmbedding,a≠b→Disjoint
        (restrictedResourceSet R (Function.Embedding.subtype (·∈T)) a)
        (restrictedResourceSet R (Function.Embedding.subtype (·∈T)) b) :=by
  subst T
  simpa [equalStateCandidateEquiv] using hM

theorem equal_state_candidate_filter_card (R:C→Finset V) (S T:Finset V) (h:S=T)
    (M:Finset (RestrictedResource R (Function.Embedding.subtype (·∈S)))) (p:C→Prop) [DecidablePred p]:
    ((M.map (equalStateCandidateEquiv R S T h).toEmbedding).filter (fun c=>p c.val)).card=
      (M.filter (fun c=>p c.val)).card :=by
  subst T
  simp [equalStateCandidateEquiv]
end Oberwolfach
