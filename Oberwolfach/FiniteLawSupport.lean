module

public import Oberwolfach.FiniteUniform

@[expose] public section

/-! Removing zero-mass outcomes changes neither probabilities nor
expectations. This lets deterministic statements be used on every sampled
regularization outcome, without adding a regularity assumption. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_sum_positive_support {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (g : Ω → ℝ) (hg : ∀ ω, μ.mass ω = 0 → g ω = 0) :
    (∑ ω : {ω : Ω // 0 < μ.mass ω}, g ω.1) = ∑ ω, g ω := by
  apply Fintype.sum_of_injective Subtype.val Subtype.val_injective
  · intro ω hω
    apply hg ω
    by_contra hn
    exact hω ⟨⟨ω, lt_of_le_of_ne (μ.nonneg ω) (Ne.symm hn)⟩, rfl⟩
  · intro ω; rfl

def FiniteLaw.support {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) :
    FiniteLaw {ω : Ω // 0 < μ.mass ω} where
  mass ω := μ.mass ω.1
  nonneg ω := μ.nonneg ω.1
  total := (finiteLaw_sum_positive_support μ μ.mass (fun _ h => h)).trans μ.total

theorem finiteLaw_support_probability {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (A : Ω → Prop) :
    μ.support.probability (fun ω => A ω.1) = μ.probability A := by
  unfold FiniteLaw.probability
  exact finiteLaw_sum_positive_support μ (fun ω => if A ω then μ.mass ω else 0)
    (by intro ω h; simp [h])

theorem finiteLaw_support_expectation {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (f : Ω → ℝ) :
    μ.support.expectation (fun ω => f ω.1) = μ.expectation f := by
  unfold FiniteLaw.expectation
  exact finiteLaw_sum_positive_support μ (fun ω => μ.mass ω * f ω)
    (by intro ω h; simp [h])

theorem finiteLaw_support_nonempty {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) : Nonempty {ω : Ω // 0 < μ.mass ω} := by
  have h : 0 < ∑ ω, μ.mass ω := by rw [μ.total]; norm_num
  obtain ⟨ω, _, hω⟩ := (Finset.sum_pos_iff_of_nonneg (fun ω _ => μ.nonneg ω)).mp h
  exact ⟨⟨ω, hω⟩⟩

end Oberwolfach
