module

public import Oberwolfach.OrdinaryAsymmetricGeometryWithInitialStatic
public import Oberwolfach.OrdinaryAsymmetricParentMarginCoefficientChoice
public import Oberwolfach.OrdinaryAsymmetricSampledCoverGeometryLateRateAndCap

@[expose] public section
/-! Parent margins and late sampling rate share the previously fixed geometry. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 60000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_asymmetric_parent_margin_with_initial_static
    (mWheel loadK d k:ℕ) (ρ₀ βparent b B εparent gap δcut βout ξreserve ζout edit:ℝ)
    (hρ₀:0<ρ₀) (hδcut:0<δcut) (hξreserve:0<ξreserve) (hedit:0<edit)
    (hgeom:∀pcap:ℝ,0<pcap→∃p:ℝ,0<p ∧ p≤1 ∧ p≤pcap ∧
      ∀η:ℝ,0<η→∃eps γ:ℝ,0<eps ∧ eps≤1 ∧ 0<γ ∧
      OrdinaryVortexBufferedRootStaticGeometrySeparateAtScale (mWheel+1) k 2 ρ₀ βparent b B εparent gap
        βout ξreserve ζout edit p η eps γ):
    ∀root eParent hParent εcap ζh ζe γ:ℝ,0<root→0<eParent→0<hParent→0<εcap→0<ζh→0<ζe→0<γ→γ≤eParent→
    ∃cMatch eCleanup hCleanup:ℝ,0<cMatch ∧ 0<eCleanup ∧ 0<hCleanup ∧
      eCleanup=eParent/2 ∧ hCleanup=hParent/2 ∧
      cMatch≤min (ζh*γ*(1/4:ℝ)) (ζe*(1/4:ℝ))/2 ∧
    ∃lam ε βe βh θmatch:ℝ,βe=eCleanup*ε ∧ βh=hCleanup*ε ∧ 0<βe ∧ 0<βh ∧
      0<lam ∧ lam≤root ∧ lam≤1/4 ∧ lam≤(ρ₀/8)/2 ∧ lam≤βe/4 ∧ lam≤βh/2 ∧
      3*(((loadK:ℝ)+1)*lam)≤edit/4 ∧ lam*((mWheel:ℝ)+1)≤edit/4 ∧
      0<ε ∧ ε≤εcap ∧ ε<1/4 ∧ ε≤ξreserve/2 ∧ ε≤ξreserve*(ρ₀/8)/2 ∧ 2*ε^2≤lam ∧
      θmatch=cMatch*ε ∧ 0<θmatch ∧
    ∀rate pcap:ℝ,0<rate→0<pcap→
    ∃ellCap kcap pbound pbar:ℝ,ellCap=θmatch/64 ∧ 0<ellCap ∧ 0<kcap ∧ 0<pbound ∧ pbound≤pcap ∧
      0<pbar ∧ pbar≤1 ∧ pbar≤pbound ∧
    ∀p:ℝ,0<p→p≤pbar→∀othercap:ℝ,0<othercap→∃εsup finishCap δsample loadCap:ℝ,0<p ∧ p≤pbound ∧ p≤1 ∧ p≤4*θmatch ∧
      20*Real.sqrt (2*p)≤θmatch/2 ∧ 0<εsup ∧ εsup≤p^2/4 ∧
      0<finishCap ∧ finishCap≤othercap ∧ finishCap≤ellCap ∧ 0<δsample ∧ 0<loadCap ∧ loadCap≤1 ∧ loadCap≤finishCap ∧
      (∀n ηrate ellrate:ℝ,0≤n→ηrate≤ellCap→ellrate≤ellCap→
        βe*n+3*max (ηrate*n) (ellrate*n)≤(eParent*ε)*n ∧
        βh*n+2*(ellrate*n)≤(hParent*ε)*n) ∧
      (∀τ ν η ell:ℝ,0≤τ→0≤ν→0≤η→0≤ell→τ≤finishCap→ν≤finishCap→η≤finishCap→ell≤ellCap→
        τ+ν≤p^2/4 ∧ τ+ν+(p*ell+δsample)≤θmatch*p/4 ∧ ν+η≤θmatch*p/4) ∧
      (∀ν:ℝ,0≤ν→ν≤finishCap→∃N:ℕ,∀n:ℕ,N≤n→
        2≤θmatch*p*n/4 ∧ ∃K Dmax:ℕ,0<K ∧ (2*p)*n≤(Dmax:ℝ) ∧ (Dmax:ℝ)≤kcap^2*n ∧
        ∀(Lconf t η:ℝ),Lconf≤kcap^2*n→t≤ν*n→0≤η→η≤finishCap→
          ((n*Dmax*(mWheel+1):ℕ):ℝ)/(K:ℝ)+
            (((mWheel+1:ℕ):ℝ)+3)*(Lconf+1)+2*(2*((2*p)*n)+2*((K+Dmax:ℕ):ℝ))+
            (Dmax:ℝ)+((Dmax*(mWheel+1):ℕ):ℝ)+3*Dmax < (βe/4)*n-3*t ∧
          ν*n+η*n+2*((2*p)*n)+((3*(K+Dmax)+Dmax*(mWheel+1):ℕ):ℝ)≤rate*n) ∧
    ∀ηpack:ℝ,0<ηpack→∃εout γgeom aLoad ξroot η₀ ηbal ηInitial βcap δcap:ℝ,
      0<εout ∧ εout≤1 ∧ 0<γgeom ∧ 0<aLoad ∧ aLoad≤1 ∧ aLoad≤loadCap ∧ aLoad≤γgeom/1000 ∧
      aLoad≤edit/(72*((mWheel:ℝ)+2)) ∧ ξroot=min (ε/200) (aLoad^2/160) ∧
      0<ξroot ∧ ξroot≤ε/100 ∧ ξroot≤γgeom/160000 ∧ 80*ξroot≤aLoad^2 ∧
      max (18*aLoad+3*(((loadK:ℝ)+1)*lam)) ((3*aLoad+lam)*((mWheel:ℝ)+1))≤ellCap ∧ 10*ξroot≤finishCap ∧
      η₀=δcut*(ρ₀/8)*ξroot/1000 ∧ 0<η₀ ∧ 0<ηbal ∧ ηbal≤η₀ ∧ ηbal≤γgeom/1000 ∧
      0<ηInitial ∧ ηInitial≤ηbal ∧ 0<βcap ∧ βcap≤1/4 ∧ βcap≤γgeom/1000 ∧ 0<δcap ∧ δcap≤γgeom/1000 ∧
    OrdinaryVortexBufferedRootStaticGeometrySeparateAtScale (mWheel+1) k 2 ρ₀ βparent b B εparent gap
      βout ξreserve ζout edit p ηpack εout γgeom ∧
    ∀(β εR εH pH:ℝ),0≤β→β≤βcap→0≤εR→εR≤δcap→0≤εH→εH≤δcap→0≤pH→pH≤1→
      OrdinaryVortexTwoStepSharpGeometryAtRatesGeneralLoad mWheel loadK d k β ε ρ₀ lam ξreserve ξroot aLoad ηbal ηInitial γgeom edit p βe βh pH εR εH
        βparent b B εparent gap βout ζout ηpack εout :=by
  have hchoose:=ordinary_asymmetric_geometry_with_initial_static mWheel loadK d k
    ρ₀ βparent b B εparent gap δcut βout ξreserve ζout edit hρ₀ hδcut hξreserve hedit hgeom
  intro root eParent hParent εcap ζh ζe γ hroot heParent hhParent hεcap hζh hζe hγ hγParent
  obtain ⟨cMatch,eCleanup,hCleanup,hc,he,hh,heEq,hhEq,hcCap,hmargin⟩:=
    ordinary_asymmetric_parent_margin_coefficient_choice ζh ζe γ eParent hParent hζh hζe hγ heParent hhParent
  obtain ⟨lam,ε,βe,βh,θmatch,hβeEq,hβhEq,hβe,hβh,hlam,hrootBound,hlam1,hlamρ,hlame,hlamh,hrow,hlevel,
    hε,hεbound,hε1,hεξ,hερ,hεroot,hθeq,hθ,hchoose⟩:=hchoose root eCleanup hCleanup εcap cMatch hroot he hh hεcap hc
  refine ⟨cMatch,eCleanup,hCleanup,hc,he,hh,heEq,hhEq,hcCap,lam,ε,βe,βh,θmatch,
    hβeEq,hβhEq,hβe,hβh,hlam,hrootBound,hlam1,hlamρ,hlame,hlamh,hrow,hlevel,
    hε,hεbound,hε1,hεξ,hερ,hεroot,hθeq,hθ,?_⟩
  intro rate pcap hrate hpcap
  obtain ⟨ellCap,kcap,pbound,pbar,hellEq,hell,hkcap,hpbound,hpcapBound,hpbar,hpbar1,hpbarBound,hchoose⟩:=
    hchoose rate pcap hrate hpcap
  refine ⟨ellCap,kcap,pbound,pbar,hellEq,hell,hkcap,hpbound,hpcapBound,hpbar,hpbar1,hpbarBound,?_⟩
  intro p hp hpbar' othercap hother
  have hcap':0<min othercap (θmatch/64):=lt_min hother (by positivity)
  obtain ⟨εsup,finishCap,δsample,loadCap,hp',hpbound',hp1,hpθ,hsqrt,hεsup,hεsupCap,
    hfinish,hfinishCap,hδsample,hload,hload1,hloadCap,hrates,hcapacity,hgeom⟩:=hchoose p hp hpbar' (min othercap (θmatch/64)) hcap'
  have hfinishOther:finishCap≤othercap:=hfinishCap.trans (min_le_left _ _)
  have hfinishEll:finishCap≤ellCap:=by rw [hellEq];exact hfinishCap.trans (min_le_right _ _)
  refine ⟨εsup,finishCap,δsample,loadCap,
    hp,hpbound',hp1,hpθ,hsqrt,hεsup,hεsupCap,hfinish,hfinishOther,hfinishEll,hδsample,hload,hload1,hloadCap,?_,hrates,hcapacity,hgeom⟩
  intro n ηrate ellrate hn hη hellrate
  have hη':ηrate≤cMatch*ε/64:=by rw [←hθeq,←hellEq];exact hη
  have hell':ellrate≤cMatch*ε/64:=by rw [←hθeq,←hellEq];exact hellrate
  have hh:=hmargin ε n ηrate ellrate hε.le hn hη' hell'
  simpa only [hβeEq,hβhEq] using hh
end Oberwolfach
