module

public import Oberwolfach.RegularCycleIsomorphism

@[expose] public section
/-! Extend previously chosen cyclic orders on distinct selected components to
all components of a two-regular factor. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def extendComponentCycleChoices {X I:Type*} [Fintype X] [DecidableEq X]
    (G:SimpleGraph X) (hG:G.IsRegularOfDegree 2)
    (components:I↪G.ConnectedComponent)
    (e:∀i:I,SimpleGraph.cycleGraph (Fintype.card (components i)) ≃g (components i).toSimpleGraph)
    (C:G.ConnectedComponent):SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph :=
  if h:∃i,components i=C then
    (Classical.choose_spec h) ▸ e (Classical.choose h)
  else Classical.choice (component_regular_two_cycle_iso G hG C).2

theorem extend_component_cycle_choices_selected {X I:Type*} [Fintype X] [DecidableEq X]
    (G:SimpleGraph X) (hG:G.IsRegularOfDegree 2)
    (components:I↪G.ConnectedComponent)
    (e:∀i:I,SimpleGraph.cycleGraph (Fintype.card (components i)) ≃g (components i).toSimpleGraph)
    (i:I):extendComponentCycleChoices G hG components e (components i)=e i:=by
  unfold extendComponentCycleChoices
  have h:∃j,components j=components i:=⟨i,rfl⟩
  rw [dif_pos h]
  have hi:Classical.choose h=i:=components.injective (Classical.choose_spec h)
  have ht:∀j (hj:components j=components i),j=i→hj ▸ e j=e i:=by
    intro j hj hji
    subst j
    cases hj
    rfl
  exact ht (Classical.choose h) (Classical.choose_spec h) hi
end Oberwolfach
