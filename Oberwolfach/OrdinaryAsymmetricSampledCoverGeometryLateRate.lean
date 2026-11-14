module

public import Oberwolfach.OrdinaryVortexRootStaticGeometryRateMonotone
public import Oberwolfach.OrdinaryAsymmetricSampledCoverOrderedChoiceWithLoadCap
public import Oberwolfach.OrdinaryVortexTwoStepSharpGeometryAtRatesGeneralLoad
public import Oberwolfach.OrdinarySharpFineBalanceRatesChoice

@[expose] public section
/-! Use one preselected static geometry in the ordered fine-cover rates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 60000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_asymmetric_sampled_cover_geometry_hierarchy_with_late_rate
    (mWheel loadK d k:ℕ) (ρ₀ βparent b B εparent gap δcut βout ξreserve ζout edit:ℝ)
    (hρ₀:0<ρ₀) (hδcut:0<δcut) (hξreserve:0<ξreserve) (hedit:0<edit)
    (hgeom:∀pcap:ℝ,0<pcap→∃p:ℝ,0<p ∧ p≤1 ∧ p≤pcap ∧
      ∀η:ℝ,0<η→∃eps γ:ℝ,0<eps ∧ eps≤1 ∧ 0<γ ∧
      OrdinaryVortexBufferedRootStaticGeometrySeparateAtScale (mWheel+1) k 2 ρ₀ βparent b B εparent gap
        βout ξreserve ζout edit p η eps γ):
    ∀root eCoeff hCoeff εcap cMatch:ℝ,0<root→0<eCoeff→0<hCoeff→0<εcap→0<cMatch→
    ∃lam ε βe βh θmatch:ℝ,βe=eCoeff*ε ∧ βh=hCoeff*ε ∧ 0<βe ∧ 0<βh ∧
      0<lam ∧ lam≤root ∧ lam≤1/4 ∧ lam≤(ρ₀/8)/2 ∧ lam≤βe/4 ∧ lam≤βh/2 ∧
      3*(((loadK:ℝ)+1)*lam)≤edit/4 ∧ lam*((mWheel:ℝ)+1)≤edit/4 ∧
      0<ε ∧ ε≤εcap ∧ ε<1/4 ∧ ε≤ξreserve/2 ∧ ε≤ξreserve*(ρ₀/8)/2 ∧ 2*ε^2≤lam ∧
      θmatch=cMatch*ε ∧ 0<θmatch ∧
    ∀rate pcap othercap:ℝ,0<rate→0<pcap→0<othercap→
    ∃ellCap kcap pbound pbar:ℝ,ellCap=θmatch/64 ∧ 0<ellCap ∧ 0<kcap ∧ 0<pbound ∧ pbound≤pcap ∧
      0<pbar ∧ pbar≤1 ∧ pbar≤pbound ∧
    ∀p:ℝ,0<p→p≤pbar→∃εsup finishCap δsample loadCap:ℝ,0<p ∧ p≤pbound ∧ p≤1 ∧ p≤4*θmatch ∧
      20*Real.sqrt (2*p)≤θmatch/2 ∧ 0<εsup ∧ εsup≤p^2/4 ∧ 0<finishCap ∧ finishCap≤othercap ∧
      0<δsample ∧ 0<loadCap ∧ loadCap≤1 ∧ loadCap≤finishCap ∧
      (∀τ ν η ell:ℝ,0≤τ→0≤ν→0≤η→0≤ell→τ≤finishCap→ν≤finishCap→η≤finishCap→ell≤ellCap→
        τ+ν≤p^2/4 ∧ τ+ν+(p*ell+δsample)≤θmatch*p/4 ∧ ν+η≤θmatch*p/4) ∧
      (∀ν:ℝ,0≤ν→ν≤finishCap→∃N:ℕ,∀n:ℕ,N≤n→
        2≤θmatch*p*n/4 ∧ ∃K Dmax:ℕ,0<K ∧ (2*p)*n≤(Dmax:ℝ) ∧ (Dmax:ℝ)≤kcap^2*n ∧
        ∀(Lconf t η:ℝ),Lconf≤kcap^2*n→t≤ν*n→0≤η→η≤finishCap→
          ((n*Dmax*(mWheel+1):ℕ):ℝ)/(K:ℝ)+
            (((mWheel+1:ℕ):ℝ)+3)*(Lconf+1)+2*(2*((2*p)*n)+2*((K+Dmax:ℕ):ℝ))+
            (Dmax:ℝ)+((Dmax*(mWheel+1):ℕ):ℝ)+3*Dmax < (βe/4)*n-3*t ∧
          ν*n+η*n+2*((2*p)*n)+((3*(K+Dmax)+Dmax*(mWheel+1):ℕ):ℝ)≤rate*n) ∧
    ∀ηpack:ℝ,0<ηpack→∃εout γ aLoad ξroot η₀ ηbal ηInitial βcap δcap:ℝ,
      0<εout ∧ εout≤1 ∧ 0<γ ∧ 0<aLoad ∧ aLoad≤1 ∧ aLoad≤loadCap ∧ aLoad≤γ/1000 ∧
      aLoad≤edit/(72*((mWheel:ℝ)+2)) ∧ ξroot=min (ε/200) (aLoad^2/160) ∧
      0<ξroot ∧ ξroot≤ε/100 ∧ ξroot≤γ/160000 ∧ 80*ξroot≤aLoad^2 ∧
      max (18*aLoad+3*(((loadK:ℝ)+1)*lam)) ((3*aLoad+lam)*((mWheel:ℝ)+1))≤ellCap ∧ 10*ξroot≤finishCap ∧
      η₀=δcut*(ρ₀/8)*ξroot/1000 ∧ 0<η₀ ∧ 0<ηbal ∧ ηbal≤η₀ ∧ ηbal≤γ/1000 ∧
      0<ηInitial ∧ ηInitial≤ηbal ∧ 0<βcap ∧ βcap≤1/4 ∧ βcap≤γ/1000 ∧ 0<δcap ∧ δcap≤γ/1000 ∧
    ∀(β εR εH pH:ℝ),0≤β→β≤βcap→0≤εR→εR≤δcap→0≤εH→εH≤δcap→0≤pH→pH≤1→
      OrdinaryVortexTwoStepSharpGeometryAtRatesGeneralLoad mWheel loadK d k β ε ρ₀ lam ξreserve ξroot aLoad ηbal ηInitial γ edit p βe βh pH εR εH
        βparent b B εparent gap βout ζout ηpack εout :=by
  intro root eCoeff hCoeff εcap cMatch hroot heCoeff hhCoeff hεcap hcMatch
  let root':=min root ((ρ₀/8)/2)
  let εcap':=min εcap (min (ξreserve/2) (ξreserve*(ρ₀/8)/2))
  have hroot':0<root':=by dsimp [root'];positivity
  have hεcap':0<εcap':=by dsimp [εcap'];positivity
  obtain ⟨lam,ε,βe,βh,θmatch,hε,hεsmall,hε1,hlameq,hlam,hlamroot,hlam1,hβeeq,hβheq,hβe,hβh,hlame,hlamh,hrow,hlevel,hθeq,hθ,hchoose⟩:=
    ordinary_asymmetric_sampled_cover_ordered_choice_with_load_cap mWheel loadK root' edit eCoeff hCoeff εcap' cMatch
      hroot' hedit heCoeff hhCoeff hεcap' hcMatch
  have hrootBound:lam≤root:=hlamroot.trans (min_le_left _ _)
  have hlamρ:lam≤(ρ₀/8)/2:=hlamroot.trans (min_le_right _ _)
  have hεbound:ε≤εcap:=hεsmall.trans (min_le_left _ _)
  have hεξ:ε≤ξreserve/2:=hεsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hερ:ε≤ξreserve*(ρ₀/8)/2:=hεsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hεroot:2*ε^2≤lam:=le_of_eq hlameq.symm
  refine ⟨lam,ε,βe,βh,θmatch,hβeeq,hβheq,hβe,hβh,hlam,hrootBound,hlam1,hlamρ,hlame,hlamh,hrow,hlevel,
    hε,hεbound,hε1,hεξ,hερ,hεroot,hθeq,hθ,?_⟩
  intro rate pcap othercap hrate hpcap hother
  obtain ⟨ellCap,kcap,pbound,hellEq,hell,hkcap,hpbound,hpcapBound,hchoose⟩:=hchoose rate pcap othercap hrate hpcap hother
  obtain ⟨pbar,hpbar,hpbar1,hpbarBound,hgeom⟩:=hgeom pbound hpbound
  refine ⟨ellCap,kcap,pbound,pbar,hellEq,hell,hkcap,hpbound,hpcapBound,hpbar,hpbar1,hpbarBound,?_⟩
  intro p hp hpbar'
  have hpbound':p≤pbound:=hpbar'.trans hpbarBound
  obtain ⟨εsup,finishCap,δsample,loadCap,hp1',hpκ,hsqrt,hεsup,hεsupCap,hfinish,hfinishCap,hδsample,hload,hload1,hloadCap,hcover,hrates,hcapacity⟩:=
    hchoose p hp hpbound'
  refine ⟨εsup,finishCap,δsample,loadCap,
    hp,hpbound',hp1',hpκ,hsqrt,hεsup,hεsupCap,hfinish,hfinishCap,hδsample,hload,hload1,hloadCap,hrates,hcapacity,?_⟩
  intro ηpack hηpack
  obtain ⟨εout,γ,hεout,hεout1,hγ,hgeomBar⟩:=hgeom ηpack hηpack
  have hgeom:=ordinary_vortex_buffered_root_static_geometry_sampling_rate_mono (mWheel+1) k 2
    ρ₀ βparent b B εparent gap βout ξreserve ζout edit pbar p ηpack εout γ hp.le hpbar' hgeomBar
  let aCap:=min (edit/(72*((mWheel:ℝ)+2))) loadCap
  have haCap:0<aCap:=by dsimp [aCap];positivity
  obtain ⟨aLoad,ξroot,η₀,ηbal,ηInitial,ha,ha1,hacap,haγ,hξeq,hξ,hξγ,hηeq,hη₀,hηbal,hηbalcap,hηγ,hηInitial,hηInitialCap,hsmall,hsmall'⟩:=
    ordinary_sharp_fine_balance_rates_choice ε δcut ρ₀ γ aCap hε hδcut hρ₀ hγ haCap
  have hacapEdit:aLoad≤edit/(72*((mWheel:ℝ)+2)):=hacap.trans (min_le_left _ _)
  have hacapLoad:aLoad≤loadCap:=hacap.trans (min_le_right _ _)
  have hξeps:ξroot≤ε/100:=by rw [hξeq];have hh:=min_le_left (ε/200) (aLoad^2/160);linarith
  have hξload:80*ξroot≤aLoad^2:=by rw [hξeq];have hh:=min_le_right (ε/200) (aLoad^2/160);nlinarith [sq_nonneg aLoad]
  have hξload':ξroot≤aLoad^2/160:=by rw [hξeq];exact min_le_right _ _
  have ⟨hellRate,hcoverRate⟩:=hcover aLoad ξroot ha.le hacapLoad hξ.le hξload'
  let βcap:ℝ:=min (1/8:ℝ) (γ/2000)
  let δcap:ℝ:=γ/2000
  have hβcap:0<βcap:=by dsimp [βcap];positivity
  have hβcap1:βcap≤1/4:=by have hh:=min_le_left (1/8:ℝ) (γ/2000);dsimp [βcap];linarith
  have hβcapγ:βcap≤γ/1000:=by have hh:=min_le_right (1/8:ℝ) (γ/2000);dsimp [βcap];linarith
  have hδcap:0<δcap:=by dsimp [δcap];positivity
  have hδcapγ:δcap≤γ/1000:=by dsimp [δcap];linarith
  refine ⟨εout,γ,aLoad,ξroot,η₀,ηbal,ηInitial,βcap,δcap,hεout,hεout1,hγ,ha,ha1,hacapLoad,haγ,hacapEdit,hξeq,hξ,hξeps,hξγ,hξload,
    hellRate,hcoverRate,hηeq,hη₀,hηbal,hηbalcap,hηγ,hηInitial,hηInitialCap,hβcap,hβcap1,hβcapγ,hδcap,hδcapγ,?_⟩
  intro β εR εH pH hβ hβsmall hεR hεRsmall hεH hεHsmall hpH hpH1
  exact ordinary_vortex_two_step_sharp_geometry_from_rates_general_load mWheel loadK d k β ε ρ₀ lam ξreserve ξroot aLoad ηbal ηInitial γ edit p βe βh pH εR εH
    βparent b B εparent gap βout ζout ηpack εout hgeom hβ (hβsmall.trans hβcap1) hε hε1 hρ₀ hγ hlam.le hlam1 hlamρ hξreserve.le hεξ hερ hεroot
    hβe.le hβh.le hp.le hpH hpH1 hεR hεH hξ.le ha.le hηbal.le hηInitial.le hedit (hβsmall.trans hβcapγ)
    (hεRsmall.trans hδcapγ) (hεHsmall.trans hδcapγ) hξγ haγ hηγ hηInitialCap hrow hlevel hacapEdit hlame hlamh
end Oberwolfach
