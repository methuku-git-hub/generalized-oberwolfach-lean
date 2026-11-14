module

public import Oberwolfach.OrdinaryTriangleRootFreeFixedPackingGeometryFixedEll
public import Oberwolfach.OrdinaryTriangleEarlyVortexParentBudget

@[expose] public section
/-! Fix one vortex contraction, outer allowance, sampling rate and cleanup
scale for the root-free triangle certificate before the conflict size. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_root_free_shared_preselection
    (α:ℝ) (k:ℕ) (ω βout b B hpack δref εstar cLinear κe pmin bHub BHub εf ηhub ηend ζfresh εrows:ℝ)
    (hlinear:0<cLinear) (hζfresh:0<ζfresh)
    (hfamily:OrdinaryTriangleRootFreeSharpInnerAfterChoice α k ω βout b B hpack δref εstar cLinear κe pmin bHub BHub εf ηhub ηend ζfresh εrows)
    (ρ₀ βparent εparent gap ξreserve ζ edit root εcap eParent hParent γbase:ℝ)
    (hρ:0<ρ₀) (hξ:0<ξreserve) (hedit:0<edit) (hroot:0<root) (hεcap:0<εcap)
    (he:0<eParent) (hh:0<hParent) (hγ:0<γbase)
    (hgeometry:∀pcap:ℝ,0<pcap→∃p:ℝ,0<p ∧ p≤1 ∧ p≤pcap ∧
      ∀η:ℝ,0<η→∃eps γgeo:ℝ,0<eps ∧ eps≤1 ∧ 0<γgeo ∧
        OrdinaryVortexBufferedRootStaticGeometrySeparateAtScale 3 k 2 ρ₀ βparent b B εparent gap βout ξreserve ζ edit p η eps γgeo):
    ∃lam ε βe βh θmatch ellCap:ℝ,
      0<ε ∧ ε≤εcap ∧ ε<1/4 ∧ ε≤ξreserve/2 ∧ ε≤ξreserve*(ρ₀/8)/2 ∧
      lam=2*ε^2 ∧ 0<lam ∧ lam≤root ∧ lam≤1/4 ∧ lam≤(ρ₀/8)/2 ∧
      0<βe ∧ 0<βh ∧ lam≤βe/4 ∧ lam≤βh/2 ∧ 3*lam≤edit/4 ∧ lam*3≤edit/4 ∧
      0<θmatch ∧ ellCap=θmatch/64 ∧ 0<ellCap ∧ 400*lam≤ellCap ∧
      ellCap≤ζfresh*(γbase*ε)/8 ∧
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
      OrdinaryTriangleRootFreeInnerFixedPacking α k ω βout b B hpack δref εstar cLinear κe pmin bHub BHub εf ηhub ηend ζfresh εrows
        p βe βh ν capSmall εsup δsample τ :=by
  obtain ⟨lam,ε,βe,βh,θmatch,ellCap,hε,hεcap',hε1,hεξ,hερ,hlamEq,hlam,hlamroot,hlam1,hlamρ,
    hβe,hβh,hlamE,hlamH,hrow,hlevel,hθ,hellEq,hell,hwide,hellscale,hbudgets⟩:=
      ordinary_triangle_early_vortex_parent_budget ρ₀ root ξreserve edit εcap eParent hParent ζfresh γbase
        hρ hroot hξ hedit hεcap he hh hζfresh hγ
  refine ⟨lam,ε,βe,βh,θmatch,ellCap,hε,hεcap',hε1,hεξ,hερ,hlamEq,hlam,hlamroot,hlam1,hlamρ,
    hβe,hβh,hlamE,hlamH,hrow,hlevel,hθ,hellEq,hell,hwide,hellscale,?_⟩
  intro rate pcap othercap hrate hpcap hother
  let capOther:=min othercap ellCap
  have hcapOther:0<capOther:=by dsimp [capOther];positivity
  obtain ⟨p,εsup,capSmall,δsample,ν,hp,hp1,hpcap',hpκ,hsqrt,hεsup,hεsupCap,hcap,hcapOther',hδ,hν,hνcap,Norder,horder,hrest⟩:=
    ordinary_triangle_root_free_fixed_packing_geometry_fixed_ell α k ω βout b B hpack δref εstar cLinear κe pmin bHub BHub εf ηhub ηend ζfresh εrows
      hlinear hζfresh hfamily ρ₀ βparent εparent gap ξreserve ζ edit hgeometry (γbase*ε) rate pcap capOther ellCap
      (by positivity) hrate hpcap hcapOther hell hellscale
  have hcapOriginal:capSmall≤othercap:=hcapOther'.trans (min_le_left _ _)
  have hcapEll:capSmall≤ellCap:=hcapOther'.trans (min_le_right _ _)
  obtain ⟨τ,hτeq,hτ,hτcap,hτ1,hnum,eps,γgeo,heps,heps1,hγgeo,hgeo,hfixed⟩:=hrest βe βh hβe hβh
  obtain ⟨hsupport,hclass,hblock,hfinish⟩:=hnum capSmall ellCap hcap.le hell.le le_rfl le_rfl
  obtain ⟨hbudgetE,hbudgetH⟩:=hbudgets capSmall hcap.le hcapEll
  exact ⟨p,εsup,capSmall,δsample,ν,hp,hp1,hpcap',hpκ,hsqrt,hεsup,hεsupCap,hcap,hcapOriginal,hcapEll,
    hδ,hν,hνcap,Norder,horder,τ,hτeq,hτ,hτcap,hτ1,hsupport,hclass,hblock,hfinish,hbudgetE,hbudgetH,
    eps,γgeo,heps,heps1,hγgeo,hgeo,hfixed⟩
end Oberwolfach
