module

public import Oberwolfach.OrdinaryActualCertificateAfterHubStaticAt
public import Oberwolfach.OrdinaryActualCertificateGeometryStaticAt
public import Oberwolfach.OrdinaryDeepCertificateHubInputs

@[expose] public section
/-! Instantiate the certificate's hub weights, density and cleanup margins
with the constants selected for the common deep event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_actual_certificate_same_hub_static
    (mWheel loadK k:ℕ) (hm:3≤mWheel) (α βparent ω bRoot BRoot hpack δ εstar cLinear:ℝ)
    (βfreq ρ₀ hmin href δlimit a ρ θ ηProfile b B εparent gap geomCap cHub CHub:ℝ)
    (hβfreq:0<βfreq) (hβ1:βfreq≤1) (hρ₀:0<ρ₀) (hρ1:ρ₀≤1) (hcHub:0<cHub) (hCHub:0<CHub)
    (hcert:OrdinaryActualCertificateGeometryStaticAt mWheel loadK k hm α βparent ω bRoot BRoot hpack δ εstar cLinear
      ρ₀ hmin href δlimit a ρ θ (ρ₀*(βfreq/200)/2) ηProfile b B εparent gap geomCap):
    let pstar:=ρ₀*(βfreq/200)/2;
    ∃δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial βout ξreserve ζout edit:ℝ,
      0<δcut ∧ δcut<1/4 ∧ δcut≤δlimit ∧ 0<ζcut ∧ 0<εcut ∧ 0<ζlimit ∧
      0<εsample ∧ 0<εvortex ∧ εvortex<1/4 ∧ 0<cBoundary ∧ 0<cInitial ∧
      OrdinaryFixedVortexNonrootNumericAt ρ₀ hmin href a ρ θ δcut ζcut εcut ζlimit εsample εvortex ∧
      0<βout ∧ βout=βparent/2 ∧ 0<ξreserve ∧ 0<ζout ∧ 0<edit ∧ ξreserve≤geomCap ∧ ζout≤geomCap ∧
    ∃γ eParent hParent κ:ℝ,0<γ ∧ 0<eParent ∧ 0<hParent ∧ γ≤eParent ∧
      eParent≤cBoundary ∧ hParent≤cBoundary ∧ eParent≤cInitial ∧ hParent≤cInitial ∧
      0<κ ∧ κ≤1 ∧ κ≤ρ₀/8 ∧ 0<pstar ∧ pstar≤1 ∧
    ∃ηhub ζhub aEnd ηend ζlocal δend:ℝ,
      0<ηhub ∧ 0<ζhub ∧ 0<aEnd ∧ aEnd≤1 ∧ 0<ηend ∧ 0<ζlocal ∧ 0<δend ∧
      OrdinaryActualCertificateAfterHubStaticAt mWheel loadK k hm α βparent ω bRoot BRoot hpack δ εstar cLinear
        ρ₀ hmin href a ρ θ pstar ηProfile b B εparent gap
        δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial βout ξreserve ζout edit
        γ cHub (4*CHub/pstar^(3*mWheel+1)) pstar κ ηhub ζhub aEnd ηend ζlocal δend :=by
  intro pstar
  obtain ⟨δcut,ζcut,εcut,ζlimit,εsample,εvortex,cBoundary,cInitial,βout,ξreserve,ζout,edit,
    hδcut,hδcut1,hδlimit,hζcut,hεcut,hζlimit,hεsample,hεvortex,hεvortex1,hBoundary,hInitial,hNumeric,
    hβout,hβoutEq,hξreserve,hζout,hedit,hξcap,hζcap,hchoose⟩:=hcert
  obtain ⟨γ,eParent,hParent,κ,BHub,hγ,he,hh,hγe,heB,hhB,heI,hhI,hκ,hκ1,hκρ,hc,hB,hBEq,hp,hp1⟩:=
    ordinary_deep_certificate_hub_inputs mWheel βfreq ρ₀ cHub CHub cBoundary cInitial
      hβfreq hβ1 hρ₀ hρ1 hcHub hCHub hBoundary hInitial
  obtain ⟨ηhub,ζhub,aEnd,ηend,ζlocal,δend,hη,hζ,ha,ha1,hηend,hζlocal,hδend,hafter⟩:=
    hchoose γ cHub BHub pstar κ hγ hc hB hp hp1 hκ hκ1
  subst BHub
  exact ⟨δcut,ζcut,εcut,ζlimit,εsample,εvortex,cBoundary,cInitial,βout,ξreserve,ζout,edit,
    hδcut,hδcut1,hδlimit,hζcut,hεcut,hζlimit,hεsample,hεvortex,hεvortex1,hBoundary,hInitial,hNumeric,
    hβout,hβoutEq,hξreserve,hζout,hedit,hξcap,hζcap,
    γ,eParent,hParent,κ,hγ,he,hh,hγe,heB,hhB,heI,hhI,hκ,hκ1,hκρ,hp,hp1,
    ηhub,ζhub,aEnd,ηend,ζlocal,δend,hη,hζ,ha,ha1,hηend,hζlocal,hδend,hafter⟩
end Oberwolfach
