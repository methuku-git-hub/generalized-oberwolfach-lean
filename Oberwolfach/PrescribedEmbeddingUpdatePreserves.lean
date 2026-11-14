module

public import Oberwolfach.FiniteHighEventsCommon

@[expose] public section
/-! Inserting a new source vertex preserves all previously prescribed images. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem prescribed_embedding_update_preserves {X V:Type} [DecidableEq X] [DecidableEq V]
    (A:Finset X) (f:X→V) (x:X) (z:V) (hx:x∉A):
    (∀ a∈A,Function.update f x z a=f a) ∧
    (insert x A).image (Function.update f x z)=insert z (A.image f) := by
  constructor
  · intro a ha
    have hax:a≠x:=by intro he;subst a;exact hx ha
    exact Function.update_of_ne hax z f
  · ext v
    simp only [Finset.mem_image,Finset.mem_insert]
    constructor
    · rintro ⟨a,ha,hav⟩
      rcases ha with rfl|ha
      · left;simpa using hav.symm
      · right
        have hax:a≠x:=by intro he;subst a;exact hx ha
        refine ⟨a,ha,?_⟩
        simpa [Function.update_of_ne hax] using hav
    · rintro (rfl|⟨a,ha,hav⟩)
      · exact ⟨x,Or.inl rfl,by simp⟩
      · have hax:a≠x:=by intro he;subst a;exact hx ha
        exact ⟨a,Or.inr ha,by simpa [Function.update_of_ne hax] using hav⟩
end Oberwolfach
