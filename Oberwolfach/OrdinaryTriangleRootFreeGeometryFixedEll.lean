module

public import Oberwolfach.OrdinaryTriangleRootFreeInnerRateGeometryAlignment

@[expose] public section
/-! Keep the root geometry's ell-cap fixed before the retention rate while
selecting only the genuinely rate-dependent tolerances afterwards. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_root_free_inner_geometry_fixed_ell
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
      OrdinaryTriangleRootFreeSharpInnerAfterCleanup α k ω β b B hpack δref εstar cLinear κe pmin bHub BHub εf ηhub ηend ζfresh εrows
        p βe βh ν capSmall εsup δsample τ :=by
  obtain ⟨pGeo,hpGeo,hpGeo1,hpGeoCap,hgeo⟩:=hgeometry pcap hpcap
  obtain ⟨p,εsup,cap,hp,hp1,hpSmall,hpκ,hsqrt,hεsup,hεsupCap,hcap,hcapOther,hRates,Norder,hOrder⟩:=
    ordinary_root_first_trace_rates_monotone (κscale/2) ζfresh rate pGeo othercap (by positivity) hζfresh hrate hpGeo hother
  let capSmall:ℝ:=cap/4
  have hc:0<capSmall:=by dsimp [capSmall];positivity
  have hcCap:capSmall≤cap:=by dsimp [capSmall];linarith
  have hpκ':p≤4*ζfresh*κscale:=by nlinarith [mul_pos hζfresh hκscale]
  have hsqrt':20*Real.sqrt (2*p)≤ζfresh*κscale/2:=by nlinarith [mul_pos hζfresh hκscale]
  have hOrder':∀n:ℕ,Norder≤n→2≤ζfresh*κscale*p*n/4:=by
    intro n hn
    have hh:=hOrder n hn
    have hn0:(0:ℝ)≤n:=by positivity
    have hh0:0≤ζfresh*κscale*p*(n:ℝ):=by positivity
    nlinarith only [hh,hh0]
  refine ⟨p,εsup,capSmall,capSmall,capSmall,hp,hp1,hpSmall.trans hpGeoCap,hpκ',hsqrt',
    hεsup,hεsupCap,hc,hcCap.trans hcapOther,hc,hc,le_rfl,Norder,hOrder',?_⟩
  intro βe βh hβe hβh
  obtain ⟨τ,hτeq,hτ,hτcap,hτ1,hcleanup⟩:=hfamily p βe βh capSmall capSmall εsup capSmall
    hp hp1 hβe hβh hc hc hεsup hc
  have hnum:∀η ell:ℝ,0≤η→0≤ell→η≤capSmall→ell≤ellCap→
      τ+capSmall≤p^2/4 ∧ τ+capSmall+(p*ell+capSmall)≤ζfresh*κscale*p/4 ∧
      capSmall+η≤ζfresh*κscale*p/4 ∧ capSmall+η+4*p≤rate:=by
    intro η ell hη hell hηcap hellcap
    have hh:=hRates τ capSmall η capSmall hτ.le hc.le hη hc.le
      (hτcap.trans hcCap) hcCap (hηcap.trans hcCap) hcCap
    have hpell:p*ell≤p*(ζfresh*κscale/8):=
      mul_le_mul_of_nonneg_left (hellcap.trans hellsmall) hp.le
    refine ⟨hh.1,?_,?_,hh.2.2.2⟩
    · nlinarith only [hh.2.1,hpell]
    · have hprod:0≤ζfresh*κscale*p:=by positivity
      nlinarith only [hh.2.2.1,hprod]
  obtain ⟨eps,γgeo,heps,heps1,hγgeo,hgeo⟩:=hgeo (cLinear*τ) (by positivity)
  have hgeo':=ordinary_vortex_buffered_root_static_geometry_sampling_rate_mono 3 k 2 ρ₀ βparent b B εparent gap
    β ξ ζ edit pGeo p (cLinear*τ) eps γgeo hp.le hpSmall hgeo
  exact ⟨τ,hτeq,hτ,hτcap,hτ1,hnum,eps,γgeo,heps,heps1,hγgeo,hgeo',hcleanup⟩
end Oberwolfach
