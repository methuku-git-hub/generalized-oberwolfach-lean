module

public import Oberwolfach.MarkedInnerDeepBalanceOrderedCaps
public import Oberwolfach.MarkedVortexInitialCommonFromParentRecord
public import Oberwolfach.MarkedVortexInitialDeepFromParentRecord
public import Oberwolfach.MarkedVortexActiveTransferFixedMargin
public import Oberwolfach.MarkedVortexInitialBalanceFromSelectedParent
public import Oberwolfach.MarkedVortexInitialBoundaryFromParentRecord

@[expose] public section
/-! Once the level parameters have been fixed, choose the selector's later
correction cap below every transfer cap, independently of the still later
parent-event tolerance. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_vortex_localized_correction_cap
    (r:ℕ) (κ α ω plo klo tstar kstar ζFixed thetaDeep eta B pstar x:ℝ)
    (hκ:0<κ) (hα:0<α) (hω:0<ω) (hplo:0<plo) (hklo:0<klo)
    (htstar:0<tstar) (hζFixed:0<ζFixed) (hθ:0<thetaDeep) (hη:0<eta)
    (hB:0≤B) (hpstar:0<pstar) (hx:0<x):
    let cCommon:=Classical.choose (marked_vortex_initial_common_from_parent_record r κ α ω plo klo hκ hα hω hplo hklo)
    let cDeep:=Classical.choose (marked_vortex_initial_deep_from_parent_record r (α/2) tstar kstar ζFixed thetaDeep B pstar hζFixed hθ hB hpstar)
    let cActive:=Classical.choose (marked_vortex_active_transfer_from_parent_fixed_margin r α tstar kstar ζFixed eta B pstar hζFixed hη hB hpstar htstar)
    let cBalance:=Classical.choose (marked_inner_deep_balance_ordered_caps (r+4) x hx)
    let cBoundary:=Classical.choose (marked_vortex_initial_boundary_from_parent_record (r+12) x hx);
    ∃cap:ℝ,0<cap ∧ cap≤cCommon ∧ cap≤cDeep ∧ cap≤cActive ∧ cap≤cBalance ∧ cap≤cBoundary ∧
      ∀ζ:ℝ,0≤ζ→ζ≤cap→(κ/2)/4+33*((r+4:ℝ)+1)^4*(2*B/pstar^(2*(r+4)+1))*ζ≤κ/4 :=by
  intro cCommon cDeep cActive cBalance cBoundary
  have hCommon:0<cCommon:=(Classical.choose_spec (marked_vortex_initial_common_from_parent_record r κ α ω plo klo hκ hα hω hplo hklo)).1
  have hDeep:0<cDeep:=(Classical.choose_spec (marked_vortex_initial_deep_from_parent_record r (α/2) tstar kstar ζFixed thetaDeep B pstar hζFixed hθ hB hpstar)).1
  have hActive:0<cActive:=(Classical.choose_spec (marked_vortex_active_transfer_from_parent_fixed_margin r α tstar kstar ζFixed eta B pstar hζFixed hη hB hpstar htstar)).1
  have hBalance:0<cBalance:=(Classical.choose_spec (marked_inner_deep_balance_ordered_caps (r+4) x hx)).1
  have hBoundary:0<cBoundary:=(Classical.choose_spec (marked_vortex_initial_boundary_from_parent_record (r+12) x hx)).1
  let C:ℝ:=33*((r+4:ℝ)+1)^4*(2*B/pstar^(2*(r+4)+1))
  have hC:0≤C:=by dsimp [C];positivity
  have hden:0<8*(1+C):=by positivity
  let cap:ℝ:=min cCommon (min cDeep (min cActive (min cBalance (min cBoundary (κ/(8*(1+C)))))))
  have hcap:0<cap:=by dsimp [cap];positivity
  have hc:cap≤cCommon:=min_le_left _ _
  have hd:cap≤cDeep:=(min_le_right _ _).trans (min_le_left _ _)
  have ha:cap≤cActive:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hb:cap≤cBalance:=(min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hbd:cap≤cBoundary:=(min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hp:cap≤κ/(8*(1+C)):=(min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  refine ⟨cap,hcap,hc,hd,ha,hb,hbd,?_⟩
  intro ζ hζ hζcap
  have hscaled:ζ*(8*(1+C))≤κ:=(le_div_iff₀ hden).mp (hζcap.trans hp)
  have hp':(κ/2)/4+C*ζ≤κ/4:=by nlinarith only [hscaled,hζ]
  simpa only [C] using hp'
end Oberwolfach
