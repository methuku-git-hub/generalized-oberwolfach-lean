module

public import Oberwolfach.FiniteHighEventsCommon

@[expose] public section
/-! The number of factors containing a vertex is at most its total number
of occurrences, even when the factors have different vertex types. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem occurrence_index_projection_card_le {I:Type} [Fintype I] [DecidableEq I]
    {X:I→Type} (T:Finset (Σ i,X i)):
    (Finset.univ.filter (fun i=>∃ x:X i,⟨i,x⟩∈T)).card≤T.card := by
  have heq:Finset.univ.filter (fun i=>∃ x:X i,⟨i,x⟩∈T)=T.image Sigma.fst:=by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_image]
    constructor
    · rintro ⟨x,hx⟩
      exact ⟨⟨i,x⟩,hx,rfl⟩
    · rintro ⟨⟨j,x⟩,hx,hj⟩
      cases hj
      exact ⟨x,hx⟩
  rw [heq]
  exact Finset.card_image_le
end Oberwolfach
