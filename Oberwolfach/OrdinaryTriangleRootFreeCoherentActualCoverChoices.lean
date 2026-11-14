module

public import Oberwolfach.OrdinaryTriangleRootFreeCoherentEarlyChoicesWithDomain
public import Oberwolfach.OrdinaryTriangleRootFreeRateActualCover

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 45000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryTriangleRootFreeRateActualAfterVortex
    (α:ℝ) (k:ℕ) (ω βout b B hpack δref εstar cLinear κe pmin bHub BHub εf ηhub ηend ζfresh εrows:ℝ)
    (ρ₀ βparent εparent gap ξreserve ζ edit eParent hParent γbase ε βe βh ellCap:ℝ):Prop :=
    ∀rate pcap othercap:ℝ,0<rate→0<pcap→0<othercap→
    ∃p εsup capSmall δsample ν:ℝ,
      0<p ∧ p≤1 ∧ p≤pcap ∧ p≤4*ζfresh*(γbase*ε) ∧
      20*Real.sqrt (2*p)≤ζfresh*(γbase*ε)/2 ∧
      0<εsup ∧ εsup≤p^2/4 ∧ 0<capSmall ∧ capSmall≤othercap ∧ capSmall≤ellCap ∧
      0<δsample ∧ 0<ν ∧ ν≤capSmall ∧
    ∃Norder:ℕ,(∀n:ℕ,Norder≤n→2≤ζfresh*(γbase*ε)*p*n/4) ∧
    ∃τ:ℝ,τ=ordinarySafeCleanupScale 3 p βe (βh/2) ν (min capSmall 1) ∧
      0<τ ∧ τ≤capSmall ∧ τ≤1 ∧
      τ+ν≤p^2/4 ∧ τ+ν+(p*ellCap+δsample)≤ζfresh*(γbase*ε)*p/4 ∧
      ν+capSmall≤ζfresh*(γbase*ε)*p/4 ∧ ν+capSmall+4*p≤rate ∧
      βe+3*max capSmall ellCap≤eParent*ε ∧ βh+2*ellCap≤hParent*ε ∧
    ∃eps γgeo:ℝ,0<eps ∧ eps≤1 ∧ 0<γgeo ∧
      OrdinaryVortexBufferedRootStaticGeometrySeparateAtScale 3 k 2 ρ₀ βparent b B εparent gap
        βout ξreserve ζ edit p (cLinear*τ) eps γgeo ∧
      OrdinaryTriangleRootFreeActualCoverAfterCleanup α k ω βout b B hpack δref εstar cLinear κe pmin bHub BHub εf ηhub ηend ζfresh εrows
        p βe βh ν capSmall εsup δsample τ

theorem ordinary_triangle_root_free_coherent_actual_cover_choices
    (α:ℝ) (k:ℕ) (hk:4≤k) (ω βout b B hpack δref εstar cLinear κe pmin cInner CInner εf ηhub ηend ζfresh εrows:ℝ)
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
      OrdinaryTriangleRootFreeRateActualAfterVortex α k ω βout b B hpack δref εstar cLinear κe pmin cInner (4*CInner/pmin^7)
        εf ηhub ηend ζfresh εrows ρ₀ βparent εparent gap ξreserve ζ edit eParent hParent γbase ε βe βh ellCap :=by
  obtain ⟨lam,ε,βe,βh,θmatch,ellCap,hv,hnum,hrate⟩:=
    ordinary_triangle_root_free_coherent_early_choices_with_domain α k ω βout b B hpack δref εstar cLinear κe pmin cInner CInner εf ηhub ηend ζfresh εrows
      hα hlinear hζfresh hκe hpmin hpmin1 hc hC hεf hηhub hηend hrows hrowsGeom hfamily hselector
      ρ₀ βparent εparent gap ξreserve ζ edit root εcap eParent hParent γbase otherβcap
      hρ hξ hedit hroot hεcap he hh hγ hother hgeometry
  refine ⟨lam,ε,βe,βh,θmatch,ellCap,hv,hnum,?_⟩
  exact ordinary_triangle_root_free_rate_actual_cover α k hk ω βout b B hpack δref εstar cLinear κe pmin cInner (4*CInner/pmin^7)
    εf ηhub ηend ζfresh εrows ρ₀ βparent εparent gap ξreserve ζ edit eParent hParent γbase ε βe βh ellCap hrate
end Oberwolfach
