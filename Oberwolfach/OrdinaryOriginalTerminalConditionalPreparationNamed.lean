module

public import Oberwolfach.OrdinaryOriginalTerminalConditionalPreparationAt

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_original_terminal_conditional_preparation_named
    (rstar m k d K dMin dNeed Nspace:ℕ) (hm:7≤ m) (hd:2≤ d) (hK:0<K) (hdMin:dMin≤ d)
    (βfreq ρ₀ α θhost capInner βPlace lamPlace ζPlace εearly ε βv:ℝ)
    (hβ:0<βfreq) (hρ:0<ρ₀) (hα:0<α) (hθhost:(1/2:ℝ)≤ θhost)
    (hε:0<ε) (hεearly:ε≤ εearly)
    (hEarly:OrdinaryPlacementEarlyRateData (α/2) ρ₀ (βfreq/200) capInner βPlace lamPlace ζPlace εearly dMin)
    (capEdit δ θ κ b z matchErr σbal κ' ζret lamMatch aRow γrow ξedit bMatch:ℝ)
    (hstage:OrdinaryPlacementStage m dNeed (5*ρ₀*(βfreq/200)^2/128) lamPlace ζPlace capEdit δ θ κ b z matchErr σbal κ')
    (hafter:OrdinaryPlacementAfterSpacing m d Nspace (5*ρ₀*(βfreq/200)^2/128) δ θ κ b z matchErr ζret)
    (hmatching:OrdinaryPlacementMatchingRateBounds K θ κ' b z δ matchErr lamMatch aRow γrow)
    (hda:1/θ≤ d)
    (hcolumns:OrdinaryEarlyUniformColumnsAtRate d m lamPlace ζPlace b εearly
      (min (1/1024:ℝ) (min ((5*ρ₀*(βfreq/200)^2/128)/4096) (1/2:ℝ)/8))
      θ z δ aRow γrow (θ/2) bMatch (5*ρ₀*(βfreq/200)^2/128) ξedit)
    (hξedit:0<ξedit) (hr:0<rstar) (rate ξroot:ℝ) (hrate:0≤rate) (hξroot:0≤ξroot)
    (mAbs tAbs aAbs bAbs:ℕ) : OrdinaryOriginalTerminalConditionalPreparationAt rstar m k d K hd βfreq ρ₀ α θhost ε βv
      δ θ aRow γrow σbal lamMatch lamPlace ξedit bMatch rate ξroot mAbs tAbs aAbs bAbs :=by
  exact ordinary_original_terminal_conditional_preparation rstar m k d K dMin dNeed Nspace hm hd hK hdMin
    βfreq ρ₀ α θhost capInner βPlace lamPlace ζPlace εearly ε βv hβ hρ hα hθhost hε hεearly hEarly
    capEdit δ θ κ b z matchErr σbal κ' ζret lamMatch aRow γrow ξedit bMatch hstage hafter hmatching hda hcolumns
    hξedit hr rate ξroot hrate hξroot mAbs tAbs aAbs bAbs
end Oberwolfach
