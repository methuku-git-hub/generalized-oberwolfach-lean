module

public import Oberwolfach.MarkedCommonSelectorGlobalBalanceBudget
public import Oberwolfach.MarkedCommonRetainedSpokeBudget

@[expose] public section
/-! Choose the selector's auxiliary cap before its reference and
neighbourhood errors, so both global balance and spoke losses fit. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_common_selector_combined_error_choice
    (r h:ℕ) (eta ζret:ℝ) (hη:0<eta) (hζret:0<ζret):
    ∃κaux:ℝ,0<κaux ∧ κaux≤eta/(8*((((r+4):ℕ):ℝ)+1)) ∧ κaux≤ζret ∧
    ∀κ εref εnbr:ℝ,0≤κ→κ≤κaux→εref=κ/4→0≤εnbr→εnbr≤κaux→
      0≤εref ∧ εref≤κaux ∧
      ∀(n:ℕ) (U:Type) [Fintype U],Fintype.card U≤n→
        (2*(εref*n)+2*(εnbr*Fintype.card U)≤eta*n ∧
         εref*n+εnbr*Fintype.card U≤eta*n ∧
         (((((r+4):ℕ):ℝ)+1)*(εnbr*n))≤eta*n) ∧
        ((εnbr/(2*((h:ℝ)+1)))*Fintype.card U≤ζret*n ∧
         (εnbr/(2*((h:ℝ)+1)))*n≤ζret*n) :=by
  let κaux:ℝ:=min (eta/(8*((((r+4):ℕ):ℝ)+1))) ζret/2
  have hκ:0<κaux:=by dsimp [κaux];positivity
  have hηCap:κaux≤eta/(8*((((r+4):ℕ):ℝ)+1)):=by
    dsimp [κaux]
    have hh:=min_le_left (eta/(8*((((r+4):ℕ):ℝ)+1))) ζret
    have hp:0<eta/(8*((((r+4):ℕ):ℝ)+1)):=by positivity
    linarith
  have hζCap:κaux≤ζret:=by
    dsimp [κaux]
    have hh:=min_le_right (eta/(8*((((r+4):ℕ):ℝ)+1))) ζret
    linarith
  refine ⟨κaux,hκ,hηCap,hζCap,?_⟩
  intro κ εref εnbr hk hkcap href hnbr hnbrcap
  obtain ⟨href0,hrefcap,hglobal⟩:=marked_common_selector_global_balance_budget r eta κaux κ εref εnbr
    hη hκ hk hkcap href hnbr hnbrcap hηCap
  refine ⟨href0,hrefcap,?_⟩
  intro n U _ hu
  exact ⟨hglobal n U hu,marked_common_retained_spoke_budget h εnbr ζret hnbr (hnbrcap.trans hζCap) n U hu⟩
end Oberwolfach
