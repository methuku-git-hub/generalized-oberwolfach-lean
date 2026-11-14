module

public import Oberwolfach.MarkedVortexFixedMarginLocalCorrectionCap

@[expose] public section
/-! Choose the global transfer cap without using the later inner-balance,
boundary or active-set tolerances. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_vortex_global_transfer_cap_early
    (r:ℕ) (κ α ω plo klo tstar kstar ζFixed thetaDeep B pstar:ℝ)
    (hκ:0<κ) (hα:0<α) (hω:0<ω) (hplo:0<plo) (hklo:0<klo)
    (htstar:0<tstar) (hζFixed:0<ζFixed) (hθ:0<thetaDeep)
    (hB:0≤B) (hpstar:0<pstar):
    let cCommon:=Classical.choose (marked_vortex_initial_common_from_parent_record r κ α ω plo klo hκ hα hω hplo hklo)
    let cDeep:=Classical.choose (marked_vortex_initial_deep_from_parent_record r (α/2) tstar kstar ζFixed thetaDeep B pstar hζFixed hθ hB hpstar);
    ∃cap:ℝ,0<cap ∧ cap≤cCommon ∧ cap≤cDeep ∧
      ∀ζ:ℝ,0≤ζ→ζ≤cap→(κ/2)/4+33*((r+4:ℝ)+1)^4*(2*B/pstar^(2*(r+4)+1))*ζ≤κ/4 :=by
  intro cCommon cDeep
  obtain ⟨cap,hpos,hcommon,hdeep,_,_,_,hbudget⟩:=
    marked_vortex_fixed_margin_local_correction_cap r κ α ω plo klo tstar kstar ζFixed thetaDeep (1:ℝ) B pstar (1:ℝ) (1:ℝ) (1:ℝ)
      hκ hα hω hplo hklo htstar hζFixed hθ (by norm_num) hB hpstar (by norm_num) (by norm_num) (by norm_num)
  exact ⟨cap,hpos,hcommon,hdeep,hbudget⟩
end Oberwolfach
