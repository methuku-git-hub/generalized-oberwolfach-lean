module

public import Oberwolfach.PrescribedFamilyUpdate

@[expose] public section
/-! Counting the factors containing a free image does not exceed the number
of actual source occurrences at that image. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {I X V:Type} [Fintype I] [DecidableEq I] [DecidableEq X] [DecidableEq V]

theorem prescribed_family_free_index_count (T:Finset (I×X)) (f:I→X→V) (v:V):
    (Finset.univ.filter (fun i=>∃ x,(i,x)∈T ∧ f i x=v)).card≤
      (T.filter (fun p=>f p.1 p.2=v)).card := by
  let Tᵥ:=T.filter (fun p=>f p.1 p.2=v)
  have heq:Finset.univ.filter (fun i=>∃ x,(i,x)∈T ∧ f i x=v)=Tᵥ.image Prod.fst:=by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_image]
    constructor
    · rintro ⟨x,hx,he⟩
      exact ⟨(i,x),Finset.mem_filter.mpr ⟨hx,he⟩,rfl⟩
    · rintro ⟨⟨j,x⟩,hp,hj⟩
      have hp':=(Finset.mem_filter.mp hp)
      simp only at hj
      subst j
      exact ⟨x,hp'.1,hp'.2⟩
  rw [heq]
  exact Finset.card_image_le
end Oberwolfach
