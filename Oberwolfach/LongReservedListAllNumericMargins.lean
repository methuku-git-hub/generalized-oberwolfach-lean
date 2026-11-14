module

public import Oberwolfach.LongReservedListConcentrationMargins
public import Oberwolfach.LongSharedErrorReservedListBudget

@[expose] public section
/-! Discharge the reserved-list concentration, trimming and deletion margins
at large order using the already selected common error. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_reserved_list_all_numeric_margins
    (αHost ρ₀:ℝ) (hα:0<αHost) (hρ:0<ρ₀) (m d:ℕ):
    let β:ℝ:=(min αHost (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16
    ∀(εQ ζcap:ℝ),0≤εQ→εQ≤β/32→0<ζcap→1/(100*(m:ℝ))≤β/16→
    ∃lam η ζ:ℝ,0<lam ∧ 0<η ∧ 0<ζ ∧ ζ≤ζcap ∧
      β/2+εQ+1/(100*(m:ℝ))+η≤lam ∧
    ∃N:ℕ,∀n≥N,
      (n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤αHost*(ρ₀/200)^2*n ∧
      β*n+(n:ℝ)^(3/4:ℝ)≤αHost*(ρ₀/200)^2*n*(1/100:ℝ) ∧
      (lam+2*ζ)*n≤β*n ∧ (n:ℝ)^(3/4:ℝ)≤η*n := by
  intro β εQ ζcap hε hεcap hζcap hm
  have hβ:0<β:=by dsimp [β];positivity
  obtain ⟨lam,η,ζ,hlam,hη,hηcap,hζ,hζcap',htrim,hbudget,hbudgetN⟩:=
    long_shared_error_reserved_list_budget β εQ (β/32) ζcap m hβ hε hεcap (by positivity) hζcap hm
  obtain ⟨N₁,hN₁⟩:=long_reserved_list_concentration_margins αHost ρ₀ hα hρ d
  obtain ⟨N₂,hN₂⟩:=eventually_three_quarters_and_constant_le_linear η 0 hη
  refine ⟨lam,η,ζ,hlam,hη,hζ,hζcap',htrim,max N₁ N₂,?_⟩
  intro n hn
  obtain ⟨herror,hmargin⟩:=hN₁ n (by omega)
  have hsub: (n:ℝ)^(3/4:ℝ)≤η*n:=by simpa using hN₂ n (by omega)
  exact ⟨herror,by simpa only [β] using hmargin,hbudgetN n,hsub⟩
end Oberwolfach
