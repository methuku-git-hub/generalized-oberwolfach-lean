module

public import Oberwolfach.MarkedLongCommonAgreementRestrictedBalance

@[expose] public section
/-! The selector's two reference errors can be chosen below one positive
cap that supplies all three global-balance margins. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_common_global_balance_error_budget
    (r:ℕ) (eta δ εref εnbr:ℝ)
    (hη:0<eta) (hδ:0≤δ) (href0:0≤εref) (hnbr0:0≤εnbr)
    (href:εref≤δ) (hnbr:εnbr≤δ)
    (hδcap:δ≤eta/(8*((((r+4):ℕ):ℝ)+1))):
    ∀(n:ℕ) (U:Type) [Fintype U],Fintype.card U≤n→
      2*(εref*n)+2*(εnbr*Fintype.card U)≤eta*n ∧
      εref*n+εnbr*Fintype.card U≤eta*n ∧
      (((((r+4):ℕ):ℝ)+1)*(εnbr*n))≤eta*n :=by
  intro n U _ hu
  let c:ℝ:=(((r+4):ℕ):ℝ)+1
  have hc:1≤c:=by
    dsimp [c]
    have hh:(0:ℝ)≤(r+4:ℕ):=by positivity
    linarith
  have hden:0<8*c:=by positivity
  have hscaled:δ*(8*c)≤eta:=(le_div_iff₀ hden).mp hδcap
  have hη4:4*δ≤eta:=by nlinarith only [hscaled,hδ,hc]
  have hη1:δ≤eta:=by nlinarith only [hη4,hδ]
  have hηc:c*δ≤eta:=by nlinarith only [hscaled,hδ,hc]
  have hn:0≤(n:ℝ):=by positivity
  have hu':(Fintype.card U:ℝ)≤n:=by exact_mod_cast hu
  have hRefN:=mul_le_mul_of_nonneg_right href hn
  have hNbrN:=mul_le_mul_of_nonneg_right hnbr hn
  have hNbrU:=mul_le_mul_of_nonneg_left hu' hnbr0
  have hδN:=mul_nonneg hδ hn
  have h4:=mul_le_mul_of_nonneg_right hη4 hn
  have h1:=mul_le_mul_of_nonneg_right hη1 hn
  have hcN:=mul_le_mul_of_nonneg_right hηc hn
  have hcNbr:=mul_le_mul_of_nonneg_left hNbrN (by positivity:c≥0)
  refine ⟨?_,?_,?_⟩
  · nlinarith only [hRefN,hNbrN,hNbrU,h4]
  · nlinarith only [hRefN,hNbrN,hNbrU,h4,hδN]
  · dsimp [c] at *
    nlinarith only [hcNbr,hcN]
end Oberwolfach
