module

public import Oberwolfach.MarkedBoundaryExtensionCounts

@[expose] public section
/-! A two-step ordinary join and individual marked continuations do not
alone imply a mixed marked-then-ordinary join. This concerns a proposed
proof substitution, not the manuscript theorem. -/
set_option autoImplicit false
namespace Oberwolfach

abbrev fiveWheelOrdinaryRelation (x y : Fin 6) : Prop :=
  x ≠ y ∧ ¬ ((x = 1 ∨ x = 2) ∧ y = 0)

abbrev fiveWheelMarkedRelation (x y : Fin 6) : Prop :=
  x ≠ y ∧ (y = 1 ∨ y = 2)

abbrev fiveWheelMarkedSpokes (x : Fin 6) : Prop := x = 1 ∨ x = 2

theorem ordinary_joins_and_marked_steps_do_not_imply_mixed_join :
    (∀ x : Fin 6, ∃ y, fiveWheelMarkedRelation x y ∧ fiveWheelMarkedSpokes y) ∧
    (∀ x z : Fin 6, x ≠ z → ∃ y,
      fiveWheelOrdinaryRelation x y ∧ fiveWheelOrdinaryRelation y z) ∧
    (∃ x z : Fin 6, x ≠ z ∧ ¬∃ y,
      fiveWheelMarkedRelation x y ∧ fiveWheelMarkedSpokes y ∧
      fiveWheelOrdinaryRelation y z) := by
  constructor
  · intro x
    fin_cases x <;> first | exact ⟨1,by decide⟩ | exact ⟨2,by decide⟩
  constructor
  · intro x z hxz
    fin_cases x <;> fin_cases z <;>
      first | contradiction | exact ⟨0,by decide⟩ | exact ⟨1,by decide⟩ |
        exact ⟨2,by decide⟩ | exact ⟨3,by decide⟩ | exact ⟨4,by decide⟩ |
        exact ⟨5,by decide⟩
  · refine ⟨3,0,by decide,?_⟩
    rintro ⟨y,hy⟩
    fin_cases y <;> simp_all [fiveWheelOrdinaryRelation, fiveWheelMarkedRelation,
      fiveWheelMarkedSpokes]
end Oberwolfach
