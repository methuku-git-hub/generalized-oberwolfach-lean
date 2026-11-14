module

public import Oberwolfach.ResourceRootOmittedLoads

@[expose] public section

/-! Forgetting a resource label is valid for pair bounds only when it is
injective on each candidate. Global injectivity is not required. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem resourceOmittedPairWeight_image_le {A B I : Type*}
    [Fintype A] [Fintype B] [Fintype I] [DecidableEq A] [DecidableEq B]
    (R : I → Finset A) (S : I → Finset B) (f : A → B)
    (hmem : ∀ i a,a∈R i → f a∈S i)
    (hinj : ∀ i a,a∈R i → ∀ b,b∈R i → f a=f b → a=b)
    (w : I → ℝ) (hw : ∀ i,0≤w i) (e g : A) :
    resourceOmittedPairWeight R w e g≤resourceOmittedPairWeight S w (f e) (f g) := by
  unfold resourceOmittedPairWeight
  apply Finset.sum_le_sum
  intro i _
  by_cases h : e∈R i ∧ g∈R i ∧ g≠e
  · rw [if_pos h,if_pos ⟨hmem i e h.1,hmem i g h.2.1,fun he=>h.2.2 (hinj i g h.2.1 e h.1 he)⟩]
  · rw [if_neg h]
    split_ifs <;> first | exact hw i | rfl

end Oberwolfach
