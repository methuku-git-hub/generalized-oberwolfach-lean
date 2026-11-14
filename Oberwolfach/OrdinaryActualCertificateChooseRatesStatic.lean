module

public import Oberwolfach.OrdinaryActualCertificateAfterRateStaticAt
public import Oberwolfach.OrdinaryActualCertificateAfterScaleStaticAt

@[expose] public section
/-! Fix the profile and wheel costs below the already chosen event and
parent-reference caps, while retaining the later load selection. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_actual_certificate_choose_rates_static
    (mWheel loadK k:ℕ) (hm:3≤mWheel) (α βparent ω bRoot BRoot hpack δ εstar cLinear:ℝ)
    (ρ₀ hmin href a ρ θ pmin ηProfile b B εparent gap:ℝ)
    (δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial βout ξreserve ζout edit:ℝ)
    (γ bHub BHub p₀ κ ηhub ζhub ζlocal δend:ℝ)
    (eParent hParent lam ε βe βh θmatch:ℝ)
    (hafter:OrdinaryActualCertificateAfterScaleStaticAt mWheel loadK k hm α βparent ω bRoot BRoot hpack δ εstar cLinear
      ρ₀ hmin href a ρ θ pmin ηProfile b B εparent gap
      δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial βout ξreserve ζout edit
      γ bHub BHub p₀ κ ηhub ζhub ζlocal δend eParent hParent lam ε βe βh θmatch)
    (cap costRate parentRate:ℝ) (hcap:0<cap) (hcost:0<costRate) (hparent:0<parentRate):
    ∃rateParent ζ δDeep rate:ℝ,
      0<rateParent ∧ rateParent≤δend*ε/8 ∧ rateParent≤parentRate ∧
      0<ζ ∧ ζ≤ζlimit ∧ ζ≤rateParent ∧ ζ≤cap ∧ 0<δDeep ∧ δDeep≤α ∧
      0<rate ∧ rate≤costRate ∧
      OrdinaryActualCertificateAfterRateStaticAt mWheel loadK k hm α βparent ω bRoot BRoot hpack δ εstar cLinear
        ρ₀ hmin href a ρ θ pmin ηProfile b B εparent gap
        δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial βout ξreserve ζout edit
        γ bHub BHub p₀ κ ηhub ζhub ζlocal δend eParent hParent lam ε βe βh θmatch rateParent ζ δDeep rate :=by
  let profileCap:=min cap parentRate
  have hprofile:0<profileCap:=by dsimp [profileCap]; positivity
  obtain ⟨rateParent,ζ,δDeep,rate,hrp,hrpend,hrpcap,hζ,hζlimit,hζrp,hδDeep,hδDeepα,hrate,hratecap,hremain⟩:=
    hafter profileCap costRate hprofile hcost
  have hrpParent:rateParent≤parentRate:=hrpcap.trans (min_le_right _ _)
  have hζcap:ζ≤cap:=hζrp.trans (hrpcap.trans (min_le_left _ _))
  exact ⟨rateParent,ζ,δDeep,rate,hrp,hrpend,hrpParent,hζ,hζlimit,hζrp,hζcap,hδDeep,hδDeepα,hrate,hratecap,hremain⟩
end Oberwolfach
