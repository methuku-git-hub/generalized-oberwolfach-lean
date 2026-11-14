module

public import Oberwolfach.GoodPlacementEvents

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem finiteLaw_four_events_lower {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (E₁ E₂ E₃ E₄ : Ω → Prop) (δ : ℝ)
    (h₁ : 1-δ≤μ.probability E₁) (h₂ : 1-δ≤μ.probability E₂)
    (h₃ : 1-δ≤μ.probability E₃) (h₄ : 1-δ≤μ.probability E₄) :
    1-4*δ≤μ.probability (fun σ=>E₁ σ ∧ E₂ σ ∧ E₃ σ ∧ E₄ σ) := by
  classical
  have h₃₄ := finiteLaw_good_intersection μ E₃ E₄ δ h₄
  have h₃₄' : 1-2*δ≤μ.probability (fun σ=>E₃ σ ∧ E₄ σ) := by linarith only [h₃,h₃₄]
  have h₂₃₄ := finiteLaw_good_intersection μ E₂ (fun σ=>E₃ σ ∧ E₄ σ) (2*δ) h₃₄'
  have h₂₃₄' : 1-3*δ≤μ.probability (fun σ=>E₂ σ ∧ E₃ σ ∧ E₄ σ) := by linarith only [h₂,h₂₃₄]
  have hh := finiteLaw_good_intersection μ E₁ (fun σ=>E₂ σ ∧ E₃ σ ∧ E₄ σ) (3*δ) h₂₃₄'
  linarith only [h₁,hh]

end Oberwolfach
