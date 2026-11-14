module

public import Oberwolfach.OrdinaryTriangleRootFreeGeometryFixedEll
public import Oberwolfach.OrdinaryTriangleRootFreeInnerFixedPacking

@[expose] public section
/-! The fixed early outer allowance, shared rate and fixed packing tolerance
also supply the root-free separate-cost triangle certificate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 35000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_root_free_fixed_packing_geometry_fixed_ell
    (α:ℝ) (k:ℕ) (ω β b B hpack δref εstar cLinear κe pmin bHub BHub εf ηhub ηend ζfresh εrows:ℝ)
    (hlinear:0<cLinear) (hζfresh:0<ζfresh)
    (hfamily:OrdinaryTriangleRootFreeSharpInnerAfterChoice α k ω β b B hpack δref εstar cLinear κe pmin bHub BHub εf ηhub ηend ζfresh εrows)
    (ρ₀ βparent εparent gap ξ ζ edit:ℝ)
    (hgeometry:∀pcap:ℝ,0<pcap→∃p:ℝ,0<p ∧ p≤1 ∧ p≤pcap ∧
      ∀η:ℝ,0<η→∃eps γgeo:ℝ,0<eps ∧ eps≤1 ∧ 0<γgeo ∧
        OrdinaryVortexBufferedRootStaticGeometrySeparateAtScale 3 k 2 ρ₀ βparent b B εparent gap β ξ ζ edit p η eps γgeo)
    (κscale rate pcap othercap ellCap:ℝ) (hκscale:0<κscale) (hrate:0<rate) (hpcap:0<pcap) (hother:0<othercap)
    (hellCap:0<ellCap) (hellsmall:ellCap≤ζfresh*κscale/8):
    ∃p εsup capSmall δsample ν:ℝ,
      0<p ∧ p≤1 ∧ p≤pcap ∧ p≤4*ζfresh*κscale ∧ 20*Real.sqrt (2*p)≤ζfresh*κscale/2 ∧
      0<εsup ∧ εsup≤p^2/4 ∧ 0<capSmall ∧ capSmall≤othercap ∧ 0<δsample ∧ 0<ν ∧ ν≤capSmall ∧
    ∃Norder:ℕ,(∀n:ℕ,Norder≤n→2≤ζfresh*κscale*p*n/4) ∧
    ∀βe βh:ℝ,0<βe→0<βh→
    ∃τ:ℝ,τ=ordinarySafeCleanupScale 3 p βe (βh/2) ν (min capSmall 1) ∧ 0<τ ∧ τ≤capSmall ∧ τ≤1 ∧
    (∀η ell:ℝ,0≤η→0≤ell→η≤capSmall→ell≤ellCap→
      τ+ν≤p^2/4 ∧ τ+ν+(p*ell+δsample)≤ζfresh*κscale*p/4 ∧ ν+η≤ζfresh*κscale*p/4 ∧ ν+η+4*p≤rate) ∧
    ∃eps γgeo:ℝ,0<eps ∧ eps≤1 ∧ 0<γgeo ∧
      OrdinaryVortexBufferedRootStaticGeometrySeparateAtScale 3 k 2 ρ₀ βparent b B εparent gap β ξ ζ edit p (cLinear*τ) eps γgeo ∧
      OrdinaryTriangleRootFreeInnerFixedPacking α k ω β b B hpack δref εstar cLinear κe pmin bHub BHub εf ηhub ηend ζfresh εrows
        p βe βh ν capSmall εsup δsample τ :=by
  obtain ⟨p,εsup,capSmall,δsample,ν,hp,hp1,hpcap',hpκ,hsqrt,hεsup,hεcap,hcap,hcapother,hδ,hν,hνcap,Norder,horder,hrest⟩:=
    ordinary_triangle_root_free_inner_geometry_fixed_ell α k ω β b B hpack δref εstar cLinear κe pmin bHub BHub εf ηhub ηend ζfresh εrows
      hlinear hζfresh hfamily ρ₀ βparent εparent gap ξ ζ edit hgeometry κscale rate pcap othercap ellCap
      hκscale hrate hpcap hother hellCap hellsmall
  refine ⟨p,εsup,capSmall,δsample,ν,hp,hp1,hpcap',hpκ,hsqrt,hεsup,hεcap,hcap,hcapother,hδ,hν,hνcap,Norder,horder,?_⟩
  intro βe βh hβe hβh
  obtain ⟨τ,hτeq,hτ,hτcap,hτ1,hnum,eps,γgeo,heps,heps1,hγ,hgeo,hinner⟩:=hrest βe βh hβe hβh
  exact ⟨τ,hτeq,hτ,hτcap,hτ1,hnum,eps,γgeo,heps,heps1,hγ,hgeo,
    ordinary_triangle_root_free_inner_fixed_packing α k ω β b B hpack δref εstar cLinear κe pmin bHub BHub εf ηhub ηend ζfresh εrows
      p βe βh ν capSmall εsup δsample τ hinner⟩
end Oberwolfach
