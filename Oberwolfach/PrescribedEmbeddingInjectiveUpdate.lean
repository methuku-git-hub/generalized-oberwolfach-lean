module

public import Oberwolfach.FiniteHighEventsCommon

@[expose] public section
/-! Extending a partial vertex embedding by one unused image. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem prescribed_embedding_injective_update {X V:Type} [DecidableEq X] [DecidableEq V]
    (A:Finset X) (f:X→V) (x:X) (z:V)
    (hinj:Set.InjOn f A) (hz:z∉A.image f):
    Set.InjOn (Function.update f x z) (↑(insert x A):Set X) := by
  intro a ha b hb hab
  simp only [Finset.mem_coe,Finset.mem_insert] at ha hb
  by_cases hax:a=x
  · subst a
    by_cases hbx:b=x
    · exact hbx.symm
    · have hbA:b∈A:=by rcases hb with h|h;exact False.elim (hbx h);exact h
      simp only [Function.update_self,Function.update_of_ne hbx] at hab
      exact False.elim (hz (Finset.mem_image.mpr ⟨b,hbA,hab.symm⟩))
  · by_cases hbx:b=x
    · subst b
      have haA:a∈A:=by rcases ha with h|h;exact False.elim (hax h);exact h
      simp only [Function.update_self,Function.update_of_ne hax] at hab
      exact False.elim (hz (Finset.mem_image.mpr ⟨a,haA,hab⟩))
    · have haA:a∈A:=by rcases ha with h|h;exact False.elim (hax h);exact h
      have hbA:b∈A:=by rcases hb with h|h;exact False.elim (hbx h);exact h
      simp only [Function.update_of_ne hax,Function.update_of_ne hbx] at hab
      exact hinj haA hbA hab
end Oberwolfach
