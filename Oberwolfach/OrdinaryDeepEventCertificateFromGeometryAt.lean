module

public import Oberwolfach.OrdinaryDeepEventCertificateFromGeometry

@[expose] public section
/-! Named output of the original-parameter parent geometry instantiated
with the common deep event before the placement spacing. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryDeepEventCertificateFromGeometryAt
    (mWheel Kdeep kcert:ℕ) (hm:3≤mWheel)
    (α βfreq ρ₀ αcut c C a ε₀ ρ θdeep:ℝ)
    (βparent ωcert bRoot BRoot hpack δparent εstar cLinear href δlimit ηProfile bParent BParent εparent gap geomCap:ℝ)
    (root εmax εearly capInner capξ capWeight parentRate pcap:ℝ):Prop :=
    let pstar:=ρ₀*(βfreq/200)/2;
    ∃δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial βout ξreserve ζout edit:ℝ,
      0<δcut ∧ δcut<1/4 ∧ δcut≤δlimit ∧ 0<ζcut ∧ 0<εcut ∧ 0<ζlimit ∧
      0<εsample ∧ 0<εvortex ∧ εvortex<1/4 ∧ 0<cBoundary ∧ 0<cInitial ∧
      OrdinaryFixedVortexNonrootNumericAt ρ₀ pstar href a ρ θdeep δcut ζcut εcut ζlimit εsample εvortex ∧
      0<βout ∧ βout=βparent/2 ∧ 0<ξreserve ∧ 0<ζout ∧ 0<edit ∧ ξreserve≤geomCap ∧ ζout≤geomCap ∧
    ∃γ eParent hParent κ:ℝ,0<γ ∧ 0<eParent ∧ 0<hParent ∧ γ≤eParent ∧
      eParent≤cBoundary ∧ hParent≤cBoundary ∧ eParent≤cInitial ∧ hParent≤cInitial ∧
      0<κ ∧ κ≤1 ∧ κ≤ρ₀/8 ∧ 0<pstar ∧ pstar≤1 ∧
    ∃ηhub ζhub aEnd ηend ζlocal δend:ℝ,
      0<ηhub ∧ 0<ζhub ∧ 0<aEnd ∧ aEnd≤1 ∧ 0<ηend ∧ 0<ζlocal ∧ 0<δend ∧
    ∃εcap:ℝ,0<εcap ∧ εcap≤εmax ∧ εcap≤εearly ∧ εcap≤capInner ∧ εcap≤ηhub ∧ εcap≤a ∧ εcap≤ρ₀/16 ∧
    ∃cMatch eCleanup hCleanup lam ε βe βh θmatch:ℝ,
      0<cMatch ∧ eCleanup=eParent/2 ∧ hCleanup=hParent/2 ∧
      cMatch≤min (ζhub*γ*(1/4:ℝ)) (ζlocal*(1/4:ℝ))/2 ∧
      βe=eCleanup*ε ∧ βh=hCleanup*ε ∧ 0<βe ∧ 0<βh ∧
      0<lam ∧ lam≤root ∧ lam≤1/4 ∧ lam≤(ρ₀/8)/2 ∧ lam≤βe/4 ∧ lam≤βh/2 ∧
      3*(((Kdeep:ℝ)+1)*lam)≤edit/4 ∧ lam*((mWheel:ℝ)+1)≤edit/4 ∧
      0<ε ∧ ε≤εcap ∧ ε≤εvortex ∧ ε<1/4 ∧ ε≤ξreserve/2 ∧ ε≤ξreserve*(ρ₀/8)/2 ∧ 2*ε^2≤lam ∧
      θmatch=cMatch*ε ∧ 0<θmatch ∧
      OrdinaryDeepEarlyEventCertificateLoadAt mWheel Kdeep kcert hm α ρ₀ pstar αcut c C a ε₀ ρ θdeep
        ε ηhub eParent hParent capξ capWeight βparent ωcert bRoot BRoot hpack δparent εstar cLinear
        pstar href ηProfile bParent BParent εparent gap
        δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial βout ξreserve ζout edit
        γ κ ζhub ζlocal δend lam βe βh θmatch parentRate pcap
end Oberwolfach
