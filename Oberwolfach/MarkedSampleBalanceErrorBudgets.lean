module

public import Mathlib.Tactic

@[expose] public section
/-! The sampled balance error is measured on its fixed domain, and also
fits the original ambient-order budget. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_sample_balance_error_budgets
    (c:ℕ) (epsBal ζBal etaBal x n M:ℝ)
    (heps:0≤epsBal) (hζ:0≤ζBal) (hM:0≤M) (hMn:M≤n)
    (hlocal:epsBal+(c+2:ℕ)*ζBal≤etaBal/2)
    (hambient:epsBal+(c+2:ℕ)*ζBal≤x/4):
    let err:=(epsBal+(c+2:ℕ)*ζBal)*M;
    0≤err ∧ err≤(etaBal/2)*M ∧ err≤(x/4)*n := by
  intro err
  have hcoef:0≤epsBal+(c+2:ℕ)*ζBal:=by positivity
  have hx:0≤x/4:=hcoef.trans hambient
  refine ⟨mul_nonneg hcoef hM,mul_le_mul_of_nonneg_right hlocal hM,?_⟩
  exact (mul_le_mul_of_nonneg_right hambient hM).trans (mul_le_mul_of_nonneg_left hMn hx)
end Oberwolfach
