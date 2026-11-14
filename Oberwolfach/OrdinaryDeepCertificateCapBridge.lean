module

public import Oberwolfach.OrdinaryCertificateFitsDeepInputs

@[expose] public section
/-! The caps fed to the local certificate fit the early sample event,
parent reference scale and deep-cover load simultaneously. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_deep_certificate_cap_bridge
    (capHub parentRate costRate aDeep:ℝ)
    (hHub:0<capHub) (hParent:0<parentRate) (hCost:0<costRate) (hDeep:0<aDeep):
    ∃profileCap rateCap othercap:ℝ,
      0<profileCap ∧ 0<rateCap ∧ 0<othercap ∧
      ∀localRate ζ rate finishCap loadCap aLoad:ℝ,
        localRate ≤ profileCap → ζ ≤ localRate → rate ≤ rateCap → 
        finishCap ≤ othercap → loadCap ≤ finishCap → aLoad ≤ loadCap → 
        ζ ≤ capHub ∧ localRate ≤ parentRate ∧ rate ≤ costRate ∧ aLoad ≤ aDeep :=by
  refine ⟨min capHub parentRate,costRate,aDeep,by positivity,hCost,hDeep,?_⟩
  intro localRate ζ rate finishCap loadCap aLoad hlocal hζ hrate hfinish hload ha
  exact ⟨hζ.trans (hlocal.trans (min_le_left _ _)),
    hlocal.trans (min_le_right _ _),hrate,ha.trans (hload.trans hfinish)⟩
end Oberwolfach
