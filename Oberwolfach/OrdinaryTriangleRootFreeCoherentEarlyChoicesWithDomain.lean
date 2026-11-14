module

public import Oberwolfach.OrdinaryTriangleRootFreeCoherentEarlyChoices
public import Oberwolfach.OrdinaryTriangleEndpointNumericPreselectionWithDomain

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 45000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryTriangleEndpointNumericDomainExists
    (α c C ε ρ₀ pmin ηHub eParent hParent κe ηend εf εrows othercap:ℝ):Prop :=
    ∃ξ Kdom Bweight tHub eEvent hEvent capHub:ℝ,
      0<ξ ∧ ξ<ηHub ∧ 0<Kdom ∧ 0<Bweight ∧ 0<tHub ∧ 0<eEvent ∧ 0<hEvent ∧ 0<capHub ∧
      eEvent≤eParent ∧ hEvent≤hParent ∧
      1+1/(ε/2)+1/((ε/2)*(ρ₀/8))≤Kdom ∧
      OrdinaryTriangleInnerEndpointAfterSetup α c C ε ρ₀ pmin ξ c Bweight ηHub Kdom eParent hParent capHub ∧
    ∃γold κold δ tpot lamInner bold Bold βcap:ℝ,
      OrdinaryDeepNumericParameters pmin κe (1/Kdom) ηend εf (2*Kdom)
        γold κold δ εrows tpot lamInner bold Bold ∧
      OrdinaryTriangleInnerNumericParameters pmin κe εf ηend εrows δ εrows tpot lamInner ∧
      0<βcap ∧ βcap≤othercap ∧ ∀β:ℝ,0≤β→β≤βcap→
        β≤1/4 ∧ β≤α/8 ∧ ξ+2*β<ηHub ∧ β≤2*δ*κe*pmin

theorem ordinary_triangle_root_free_coherent_early_choices_with_domain
    (α:ℝ) (k:ℕ) (ω βout b B hpack δref εstar cLinear κe pmin cInner CInner εf ηhub ηend ζfresh εrows:ℝ)
    (hα:0<α) (hlinear:0<cLinear) (hζfresh:0<ζfresh) (hκe:0<κe) (hpmin:0<pmin) (hpmin1:pmin≤1)
    (hc:0<cInner) (hC:0<CInner) (hεf:0<εf) (hηhub:0<ηhub) (hηend:0<ηend) (hrows:0<εrows)
    (hrowsGeom:εrows≤min (pmin^4/16) (pmin^3/2))
    (hfamily:OrdinaryTriangleRootFreeSharpInnerAfterChoice α k ω βout b B hpack δref εstar cLinear κe pmin
      cInner (4*CInner/pmin^7) εf ηhub ηend ζfresh εrows)
    (hselector:OrdinaryNamedTriangleInnerEndpointSelector α cInner CInner)
    (ρ₀ βparent εparent gap ξreserve ζ edit root εcap eParent hParent γbase otherβcap:ℝ)
    (hρ:0<ρ₀) (hξ:0<ξreserve) (hedit:0<edit) (hroot:0<root) (hεcap:0<εcap)
    (he:0<eParent) (hh:0<hParent) (hγ:0<γbase) (hother:0<otherβcap)
    (hgeometry:∀pcap:ℝ,0<pcap→∃p:ℝ,0<p ∧ p≤1 ∧ p≤pcap ∧
      ∀η:ℝ,0<η→∃eps γgeo:ℝ,0<eps ∧ eps≤1 ∧ 0<γgeo ∧
        OrdinaryVortexBufferedRootStaticGeometrySeparateAtScale 3 k 2 ρ₀ βparent b B εparent gap βout ξreserve ζ edit p η eps γgeo):
    ∃lam ε βe βh θmatch ellCap:ℝ,
      OrdinaryTriangleEarlyVortexData ρ₀ root ξreserve edit εcap ζfresh γbase lam ε βe βh θmatch ellCap ∧
      OrdinaryTriangleEndpointNumericDomainExists α cInner CInner ε ρ₀ pmin ηhub eParent hParent κe ηend εf εrows otherβcap ∧
      OrdinaryTriangleRootFreeRateAfterVortex α k ω βout b B hpack δref εstar cLinear κe pmin cInner (4*CInner/pmin^7)
        εf ηhub ηend ζfresh εrows ρ₀ βparent εparent gap ξreserve ζ edit eParent hParent γbase ε βe βh ellCap :=by
  obtain ⟨lam,ε,βe,βh,θmatch,ellCap,hε,hεcap',hε1,hεξ,hερ,hlamEq,hlam,hlamroot,hlam1,hlamρ,
    hβe,hβh,hlamE,hlamH,hrow,hlevel,hθ,hellEq,hell,hwide,hellscale,hrest⟩:=
      ordinary_triangle_root_free_shared_preselection α k ω βout b B hpack δref εstar cLinear κe pmin cInner (4*CInner/pmin^7)
        εf ηhub ηend ζfresh εrows hlinear hζfresh hfamily ρ₀ βparent εparent gap ξreserve ζ edit root εcap eParent hParent γbase
        hρ hξ hedit hroot hεcap he hh hγ hgeometry
  have hnum:=ordinary_triangle_endpoint_numeric_preselection_with_domain α cInner CInner ε ρ₀ pmin ηhub eParent hParent κe ηend εf εrows otherβcap
    hselector hα hc hC hε hε1 hρ hpmin hpmin1 hηhub he hh hκe hηend hεf hrows hrowsGeom hother
  refine ⟨lam,ε,βe,βh,θmatch,ellCap,?_,hnum,hrest⟩
  exact ⟨hε,hεcap',hε1,hεξ,hερ,hlamEq,hlam,hlamroot,hlam1,hlamρ,hβe,hβh,hlamE,hlamH,hrow,hlevel,
    hθ,hellEq,hell,hwide,hellscale⟩
end Oberwolfach
