module

public import Oberwolfach.DegreeCutHall
public import Oberwolfach.FiniteTypedBijection

@[expose] public section

/-! Combining two prescribed, edge-compatible class matchings. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem combine_class_matchings {A Y : Type*} [Fintype A] [Fintype Y]
    (P : A → Prop) (Q : Y → Prop) (E : A → Y → Prop)
    (f₁ : {a // P a} ≃ {y // Q y}) (f₀ : {a // ¬P a} ≃ {y // ¬Q y})
    (h₁ : ∀ a, E a.val (f₁ a).val) (h₀ : ∀ a, E a.val (f₀ a).val) :
    ∃ f : A ≃ Y, (∀ a, E a (f a)) ∧ (∀ a, Q (f a) ↔ P a) := by
  classical
  let f : A ≃ Y := (Equiv.sumCompl P).symm.trans
    ((Equiv.sumCongr f₁ f₀).trans (Equiv.sumCompl Q))
  refine ⟨f,?_,?_⟩
  · intro a
    by_cases ha : P a
    · change E a ((Equiv.sumCompl Q) ((Equiv.sumCongr f₁ f₀) ((Equiv.sumCompl P).symm a)))
      rw [Equiv.sumCompl_symm_apply_of_pos ha]
      exact h₁ ⟨a,ha⟩
    · change E a ((Equiv.sumCompl Q) ((Equiv.sumCongr f₁ f₀) ((Equiv.sumCompl P).symm a)))
      rw [Equiv.sumCompl_symm_apply_of_neg ha]
      exact h₀ ⟨a,ha⟩
  · intro a
    by_cases ha : P a
    · have he : Q (f a) := by
        change Q ((Equiv.sumCompl Q) ((Equiv.sumCongr f₁ f₀) ((Equiv.sumCompl P).symm a)))
        rw [Equiv.sumCompl_symm_apply_of_pos ha]
        exact (f₁ ⟨a,ha⟩).property
      exact ⟨fun _ => ha,fun _ => he⟩
    · have he : ¬Q (f a) := by
        change ¬Q ((Equiv.sumCompl Q) ((Equiv.sumCongr f₁ f₀) ((Equiv.sumCompl P).symm a)))
        rw [Equiv.sumCompl_symm_apply_of_neg ha]
        exact (f₀ ⟨a,ha⟩).property
      exact ⟨fun h => (he h).elim,fun h => (ha h).elim⟩

end Oberwolfach
