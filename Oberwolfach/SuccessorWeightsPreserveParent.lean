module

public import Oberwolfach.SuccessorWeightFamilies

@[expose] public section
/-! A previously chosen parent weighting can be retained in an independently
constructed family, with all other level weights unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
theorem successor_weight_family_preserve_parent
    (W:ℕ→Type) [∀ i,Fintype (W i)] (m b:ℕ)
    (G:∀ i,SimpleGraph (W i)) (π:∀ i,Equiv.Perm (W i)) (D:ℕ→ℝ)
    (τ A B:ℝ) (L:ℕ)
    (weight:∀ i,(Fin (m+1)→W i)→ℝ)
    (hw:∀ i≤L,SuccessorSequenceWeightConditions (G i) (π i) b (D i) τ A B (weight i))
    (parent:(Fin (m+1)→W 0)→ℝ)
    (hparent:SuccessorSequenceWeightConditions (G 0) (π 0) b (D 0) τ A B parent):
    ∃ updated:∀ i,(Fin (m+1)→W i)→ℝ,
      updated 0=parent ∧ (∀ i,0 < i → updated i=weight i) ∧
      ∀ i≤L,SuccessorSequenceWeightConditions (G i) (π i) b (D i) τ A B (updated i) := by
  let updated:=Function.update weight 0 parent
  refine ⟨updated,?_,?_,?_⟩
  · simp [updated]
  · intro i hi
    simp [updated,ne_of_gt hi]
  · intro i hi
    by_cases h:i=0
    · subst i
      simpa [updated] using hparent
    · simpa [updated,h] using hw i hi
end Oberwolfach
