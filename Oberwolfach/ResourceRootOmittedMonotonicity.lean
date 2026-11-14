module

public import Oberwolfach.ResourceRootOmittedLoads

@[expose] public section

/-! Deletion monotonicity uses the same candidates and weights, including
at a root absent from the smaller state. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {A I : Type*} [Fintype A] [Fintype I] [DecidableEq A]

theorem resourceRootOmittedLoad_mono (R : I → Finset A) (w : I → ℝ)
    (hw : ∀ i,0≤w i) (keep keep' : A → Prop) (hsub : ∀ f,keep' f → keep f) (e : A) :
    resourceRootOmittedLoad R w keep' e≤resourceRootOmittedLoad R w keep e := by
  unfold resourceRootOmittedLoad
  apply Finset.sum_le_sum
  intro i _
  by_cases h : e∈R i ∧ (∀ f∈R i,f≠e → keep' f)
  · rw [if_pos h,if_pos ⟨h.1,fun f hf hne=>hsub f (h.2 f hf hne)⟩]
  · rw [if_neg h]
    split_ifs <;> first | exact hw i | rfl

theorem resourceRootOmittedLoad_all (R : I → Finset A) (w : I → ℝ) (e : A) :
    resourceRootOmittedLoad R w (fun _=>True) e=∑ i,if e∈R i then w i else 0 := by
  simp only [resourceRootOmittedLoad,implies_true,and_true]

end Oberwolfach
