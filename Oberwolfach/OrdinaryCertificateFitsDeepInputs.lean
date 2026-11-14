module

public import Oberwolfach.OrdinaryFixedDeepToleranceLateVortexError

@[expose] public section
/-! The certificate's own load and edit tolerance fit the previously chosen
deep event when its two external caps are selected early enough. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_certificate_fits_deep_inputs
    (aLoad loadCap finishCap othercap aDeep ε εcap ηHub ξroot:ℝ)
    (ha:0<aLoad) (haLoad:aLoad≤loadCap) (hload:loadCap≤finishCap)
    (hfinish:finishCap≤othercap) (hother:othercap≤aDeep)
    (hη:0<ηHub) (hε:ε≤εcap) (hεcap:εcap≤ηHub) (hξ:0<ξroot) (hξscale:ξroot≤ε/100):
    0<aLoad ∧ aLoad≤aDeep ∧ 0<ξroot ∧ ξroot<ηHub :=by
  exact ⟨ha,haLoad.trans (hload.trans (hfinish.trans hother)),hξ,
    ordinary_certificate_deep_tolerance_hub_gap ε ηHub ξroot hη (hε.trans hεcap) hξscale⟩
end Oberwolfach
