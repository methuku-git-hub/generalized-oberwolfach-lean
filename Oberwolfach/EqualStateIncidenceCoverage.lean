module

public import Oberwolfach.RestrictedResourceEqualStateEquiv

@[expose] public section
/-! Equal finite resource sets identify each selected matching, its resource
union and the uncovered portion of each specified incidence set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V C:Type} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]

def equalStateResourceEquiv (S T:Finset V) (h:S=T):S≃T:=by
  subst T
  exact Equiv.refl _

theorem equal_state_candidate_covered_union
    (R:C→Finset V) (S T:Finset V) (h:S=T)
    (M:Finset (RestrictedResource R (Function.Embedding.subtype (·∈S)))):
    let e:=(equalStateResourceEquiv S T h).toEmbedding
    let q:=(equalStateCandidateEquiv R S T h).toEmbedding
    (M.map q).biUnion (restrictedResourceSet R (Function.Embedding.subtype (·∈T)))=
      (M.biUnion (restrictedResourceSet R (Function.Embedding.subtype (·∈S)))).map e :=by
  subst T
  simp [equalStateCandidateEquiv,equalStateResourceEquiv]

theorem equal_state_candidate_uncovered_incidence_card
    (R:C→Finset V) (S T:Finset V) (h:S=T)
    (M:Finset (RestrictedResource R (Function.Embedding.subtype (·∈S)))) (A:Finset S):
    let e:=(equalStateResourceEquiv S T h).toEmbedding
    let q:=(equalStateCandidateEquiv R S T h).toEmbedding
    ((A.map e)\(M.map q).biUnion (restrictedResourceSet R (Function.Embedding.subtype (·∈T)))).card=
      (A\M.biUnion (restrictedResourceSet R (Function.Embedding.subtype (·∈S)))).card :=by
  subst T
  simp [equalStateCandidateEquiv,equalStateResourceEquiv]
end Oberwolfach
