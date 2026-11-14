module

public import Oberwolfach.RestrictedResourceStateLift

@[expose] public section
/-! A lifted matching has exactly the same fixed weighted tests, not merely
identical support and unweighted counts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V C:Type} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]

theorem surviving_candidate_fixed_weighted_sum
    (R:C→Finset V) (S T:Finset V) (hST:S⊆T)
    (M:Finset (RestrictedResource R (Function.Embedding.subtype (·∈S)))) (w:C→ℝ):
    (∑a ∈ M.map (survivingCandidateEmbedding R S T hST), w a.val) =
      ∑a ∈ M, w a.val :=by
  rw [Finset.sum_map]
  rfl

theorem surviving_candidate_fixed_weighted_test
    (R:C→Finset V) (S T:Finset V) (hST:S⊆T)
    (M:Finset (RestrictedResource R (Function.Embedding.subtype (·∈S))))
    (p:C→Prop) [DecidablePred p] (w:C→ℝ):
    (∑a ∈ (M.map (survivingCandidateEmbedding R S T hST)).filter (fun c=>p c.val), w a.val) =
      ∑a ∈ M.filter (fun c=>p c.val), w a.val :=by
  classical
  have hfilter: (M.map (survivingCandidateEmbedding R S T hST)).filter (fun c=>p c.val) =
      (M.filter (fun c=>p c.val)).map (survivingCandidateEmbedding R S T hST) :=by
    ext a
    simp only [Finset.mem_filter,Finset.mem_map]
    constructor
    · rintro ⟨⟨b,hb,rfl⟩,hp⟩
      exact ⟨b,⟨hb,hp⟩,rfl⟩
    · rintro ⟨b,⟨hb,hp⟩,rfl⟩
      exact ⟨⟨b,hb,rfl⟩,hp⟩
  rw [hfilter, Finset.sum_map]
  rfl
end Oberwolfach
