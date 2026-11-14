module

public import Mathlib.Tactic

@[expose] public section
/-! One realised change allowance leaves room for both the local balance
and the original ambient error scale at every external root. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_balance_perturbation_slack
    (m:ℕ) (etaBal x iota:ℝ) (hη:0<etaBal) (hx:0<x) (hi : 0 < iota):
    ∃ ζcap:ℝ,0<ζcap ∧ ∀ ζ:ℝ,0≤ζ→ζ≤ζcap→
    ∀ n I err:ℝ,0≤n→iota*n≤I→
      err≤(etaBal/2)*I → err≤(x/4)*n →
      err+(m+4:ℕ)*ζ*n≤etaBal*I ∧ err+(m+4:ℕ)*ζ*n≤(x/2)*n := by
  let a:ℝ:=(m+4:ℕ)
  have ha:0<a:=by dsimp [a];positivity
  let ζcap:=min (etaBal*iota/(2*(a+1))) (x/(4*(a+1)))
  have hcap:0<ζcap:=by
    dsimp [ζcap]
    exact lt_min (div_pos (mul_pos hη hi) (by linarith)) (div_pos hx (by linarith))
  refine ⟨ζcap,hcap,?_⟩
  intro ζ hζ hζcap n I err hn hI heI hen
  have h1:ζ≤etaBal*iota/(2*(a+1)):=hζcap.trans (min_le_left _ _)
  have h2:ζ≤x/(4*(a+1)):=hζcap.trans (min_le_right _ _)
  have h1':ζ*(2*(a+1))≤etaBal*iota:=(le_div_iff₀ (by positivity)).mp h1
  have h2':ζ*(4*(a+1))≤x:=(le_div_iff₀ (by positivity)).mp h2
  have hmul1:=mul_le_mul_of_nonneg_right h1' hn
  have hmul2:=mul_le_mul_of_nonneg_right h2' hn
  have hmulI:=mul_le_mul_of_nonneg_left hI (show 0≤etaBal/2 by positivity)
  constructor <;> dsimp only [a] at * <;> push_cast at * <;>
    nlinarith [mul_nonneg hζ hn,mul_nonneg ha.le (mul_nonneg hζ hn)]
end Oberwolfach
