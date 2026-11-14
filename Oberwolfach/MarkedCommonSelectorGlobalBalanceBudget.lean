module

public import Oberwolfach.MarkedCommonGlobalBalanceBudget

@[expose] public section
/-! Instantiate the global-balance margins with the selector's actual
reference error and its earlier auxiliary cap. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_common_selector_global_balance_budget
    (r:ℕ) (eta κaux κ εref εnbr:ℝ)
    (hη:0<eta) (hκaux:0<κaux) (hκ:0≤κ) (hκcap:κ≤κaux)
    (href:εref=κ/4) (hnbr0:0≤εnbr) (hnbr:εnbr≤κaux)
    (hcap:κaux≤eta/(8*((((r+4):ℕ):ℝ)+1))):
    0≤εref ∧ εref≤κaux ∧
    ∀(n:ℕ) (U:Type) [Fintype U],Fintype.card U≤n→
      2*(εref*n)+2*(εnbr*Fintype.card U)≤eta*n ∧
      εref*n+εnbr*Fintype.card U≤eta*n ∧
      (((((r+4):ℕ):ℝ)+1)*(εnbr*n))≤eta*n :=by
  have href0:0≤εref:=by rw [href];positivity
  have hrefcap:εref≤κaux:=by rw [href];linarith
  exact ⟨href0,hrefcap,marked_common_global_balance_error_budget r eta κaux εref εnbr
    hη hκaux.le href0 hnbr0 hrefcap hnbr hcap⟩
end Oberwolfach
