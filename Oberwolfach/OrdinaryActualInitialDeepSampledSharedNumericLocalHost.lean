module

public import Oberwolfach.OrdinaryActualInitialDeepFineSharedNumericLocalHost
public import Oberwolfach.OrdinaryActualTraceBalanceRateMonotone
public import Oberwolfach.OrdinaryAsymmetricGeometryParentMarginHierarchyGeneralLoad
public import Oberwolfach.OrdinaryAsymmetricFinishNumericWitness

@[expose] public section
/-! Select the profile cost rate before the fresh-sampling probability,
then align the later fine cover, initial balance and root geometry choices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 80000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_actual_initial_deep_sampled_shared_numeric_local_host
    (mWheel loadK d k:ℕ) (hm:3≤mWheel) (hk:4≤k)
    (ρ₀ hmin href δlimit a ρ θ α pmin ηProfile:ℝ)
    (βparent b B εparent gap geomCap:ℝ)
    (hρ₀:0<ρ₀) (hhmin:0<hmin) (hhref:0<href) (hδlimit:0<δlimit)
    (ha:0<a) (hρ:0<ρ) (hθ:0<θ) (hα:0<α) (hpmin:0<pmin) (hηProfile:0<ηProfile)
    (hβparent:0<βparent) (hb:0<b) (hB:0≤B) (hgap:0<gap) (hcap:0<geomCap):
    ∃δcut ζcut εcut ζlimit εsample εvortex cBoundary βout ξreserve ζout edit:ℝ,
      0<δcut ∧ δcut<1/4 ∧ δcut≤δlimit ∧ 0<ζcut ∧ 0<εcut ∧ 0<ζlimit ∧
      0<εsample ∧ 0<εvortex ∧ εvortex<1/4 ∧ 0<cBoundary ∧
      OrdinaryFixedVortexNonrootNumericAt ρ₀ hmin href a ρ θ δcut ζcut εcut ζlimit εsample εvortex ∧
      0<βout ∧ βout=βparent/2 ∧ 0<ξreserve ∧ 0<ζout ∧ 0<edit ∧ ξreserve≤geomCap ∧ ζout≤geomCap ∧
    ∀root eParent hParent εcap ζh ζe γ δend:ℝ,
      0<root→0<eParent→0<hParent→0<εcap→0<ζh→0<ζe→0<γ→γ≤eParent→0<δend→
      eParent≤cBoundary→hParent≤cBoundary→
    ∃cMatch eCleanup hCleanup lam ε βe βh θmatch:ℝ,
      0<cMatch ∧ eCleanup=eParent/2 ∧ hCleanup=hParent/2 ∧
      cMatch≤min (ζh*γ*(1/4:ℝ)) (ζe*(1/4:ℝ))/2 ∧
      βe=eCleanup*ε ∧ βh=hCleanup*ε ∧ 0<βe ∧ 0<βh ∧
      0<lam ∧ lam≤root ∧ lam≤1/4 ∧ lam≤(ρ₀/8)/2 ∧ lam≤βe/4 ∧ lam≤βh/2 ∧
      3*(((loadK:ℝ)+1)*lam)≤edit/4 ∧ lam*((mWheel:ℝ)+1)≤edit/4 ∧
      0<ε ∧ ε≤εcap ∧ ε≤εvortex ∧ ε<1/4 ∧ ε≤ξreserve/2 ∧ ε≤ξreserve*(ρ₀/8)/2 ∧ 2*ε^2≤lam ∧
      θmatch=cMatch*ε ∧ 0<θmatch ∧
    ∀profileCap rateCap:ℝ,0<profileCap→0<rateCap→∃rateParent ζ δDeep rate:ℝ,
      0<rateParent ∧ rateParent≤δend*ε/8 ∧ rateParent≤profileCap ∧
      0<ζ ∧ ζ≤ζlimit ∧ ζ≤rateParent ∧ 0<δDeep ∧ δDeep≤α ∧ 0<rate ∧ rate≤rateCap ∧
    ∀pcap othercap:ℝ,0<pcap→0<othercap→
    ∃ellCap kcap pbound p εsup finishCap δsample loadCap ν cap:ℝ,
      ellCap=θmatch/64 ∧ 0<ellCap ∧ 0<kcap ∧ 0<pbound ∧ pbound≤pcap ∧
      0<p ∧ p≤pbound ∧ p≤1 ∧ p≤4*θmatch ∧ 20*Real.sqrt (2*p)≤θmatch/2 ∧
      0<εsup ∧ εsup≤p^2/4 ∧ 0<finishCap ∧ finishCap≤othercap ∧ finishCap≤ellCap ∧
      0<δsample ∧ 0<loadCap ∧ loadCap≤1 ∧ 0<ν ∧ 0<cap ∧ ν≤finishCap ∧ cap≤finishCap ∧
    ∃Nfinish:ℕ,
      (∀n:ℕ,Nfinish≤n→2≤θmatch*p*n/4 ∧
        ∃Kcap Dmax:ℕ,0<Kcap ∧ (2*p)*n≤(Dmax:ℝ) ∧ (Dmax:ℝ)≤kcap^2*n ∧
        ∀τ ηrate ellrate Lconf:ℝ,0≤τ→τ≤cap→0≤ηrate→ηrate≤finishCap→0≤ellrate→ellrate≤ellCap→
          Lconf≤kcap^2*n→
          (βe*n+3*max (ηrate*n) (ellrate*n)≤(eParent*ε)*n ∧
           βh*n+2*(ellrate*n)≤(hParent*ε)*n) ∧
          (τ+ν≤p^2/4 ∧ τ+ν+(p*ellrate+δsample)≤θmatch*p/4 ∧ ν+ηrate≤θmatch*p/4) ∧
          (((n*Dmax*(mWheel+1):ℕ):ℝ)/(Kcap:ℝ)+
            (((mWheel+1:ℕ):ℝ)+3)*(Lconf+1)+2*(2*((2*p)*n)+2*((Kcap+Dmax:ℕ):ℝ))+
            (Dmax:ℝ)+((Dmax*(mWheel+1):ℕ):ℝ)+3*Dmax < (βe/4)*n-3*(ν*n) ∧
           ν*n+ηrate*n+2*((2*p)*n)+((3*(Kcap+Dmax)+Dmax*(mWheel+1):ℕ):ℝ)≤rate*n)) ∧
    ∀ηpack:ℝ,0<ηpack→∃εout γgeom aLoad ξroot η₀ ηbal ηInitial βcap δcap δInitial:ℝ,
      0<εout ∧ εout≤1 ∧ 0<γgeom ∧ 0<aLoad ∧ aLoad≤1 ∧ aLoad≤loadCap ∧ aLoad≤γgeom/1000 ∧
      aLoad≤edit/(72*((mWheel:ℝ)+2)) ∧ ξroot=min (ε/200) (aLoad^2/160) ∧
      0<ξroot ∧ ξroot≤ε/100 ∧ ξroot≤γgeom/160000 ∧ 80*ξroot≤aLoad^2 ∧
      max (18*aLoad+3*(((loadK:ℝ)+1)*lam)) ((3*aLoad+lam)*((mWheel:ℝ)+1))≤ellCap ∧ 10*ξroot≤finishCap ∧
      η₀=δcut*(ρ₀/8)*ξroot/1000 ∧ 0<η₀ ∧ 0<ηbal ∧ ηbal≤η₀ ∧ ηbal≤γgeom/1000 ∧
      0<ηInitial ∧ ηInitial≤ηbal ∧ 0<βcap ∧ βcap≤1/4 ∧ βcap≤γgeom/1000 ∧
      0<δcap ∧ δcap≤γgeom/1000 ∧ 0<δInitial ∧ δInitial≤α ∧ δInitial≤ηInitial ∧
    ∀β:ℝ,0≤β→β≤1/4→β≤βcap→β≤δInitial→β≤δDeep→∀C:ℝ,0≤C→
    ∃mInitial mBalance mCover:ℕ,1≤mInitial ∧ 1≤mBalance ∧ 1≤mCover ∧
      OrdinaryVortexActualInitialAmbientBalanceAt ε ρ₀ α pmin hmin ηInitial cBoundary δInitial d β mInitial ∧
      OrdinaryActualTraceSeparatedBalanceAt ε ρ₀ α pmin hmin ηProfile ζ cBoundary δDeep rate d 2 β C mBalance ∧
      OrdinaryActualTraceFineCoverAtLocalBalanceLocalHost mWheel loadK 2 ρ₀ hmin href δcut ζcut εcut ζlimit εsample ε ξroot aLoad a ρ θ β ηbal d mCover ∧
    ∀εR εH pH:ℝ,0≤εR→εR≤δcap→0≤εH→εH≤δcap→0≤pH→pH≤1→
      OrdinaryVortexTwoStepSharpGeometryAtRatesGeneralLoad mWheel loadK d k β ε ρ₀ lam ξreserve ξroot aLoad ηbal ηInitial γgeom edit p βe βh pH εR εH
        βparent b B εparent gap βout ζout ηpack εout :=by
  obtain ⟨δcut,ζcut,εcut,ζlimit,εsample,εvortex,cBoundary,hδcut,hδcut1,hδlimit',hζcut,hεcut,hζlimit,
    hεsample,hεvortex,hεvortex1,hcBoundary,hNumeric,hDeep⟩:=
    ordinary_actual_initial_deep_fine_shared_numeric_local_host mWheel loadK 2 hm (by omega)
      ρ₀ hmin href δlimit a ρ θ α pmin ηProfile d hρ₀ hhmin hhref hδlimit ha hρ hθ hα hpmin hηProfile
  obtain ⟨βout,ξreserve,ζout,edit,hβout,hβeq,hξreserve,hζout,hedit,hξcap,hζcap,hGeom⟩:=
    ordinary_asymmetric_geometry_parent_margin_hierarchy_general_load mWheel loadK d k hk ρ₀ βparent b B εparent gap geomCap δcut
      hρ₀ hβparent hb hB hgap hcap hδcut
  refine ⟨δcut,ζcut,εcut,ζlimit,εsample,εvortex,cBoundary,βout,ξreserve,ζout,edit,
    hδcut,hδcut1,hδlimit',hζcut,hεcut,hζlimit,hεsample,hεvortex,hεvortex1,hcBoundary,hNumeric,
    hβout,hβeq,hξreserve,hζout,hedit,hξcap,hζcap,?_⟩
  intro root eParent hParent εcap ζh ζe γ δend hroot heParent hhParent hεcap hζh hζe hγ hγParent hδend heBound hhBound
  have hεcap':0<min εcap εvortex:=lt_min hεcap hεvortex
  obtain ⟨cMatch,eCleanup,hCleanup,hc,he,hh,heEq,hhEq,hcCap,lam,ε,βe,βh,θmatch,
    hβeEq,hβhEq,hβe,hβh,hlam,hrootBound,hlam1,hlamρ,hlame,hlamh,hrow,hlevel,
    hε,hεbound,hε1,hεξ,hερ,hεroot,hθeq,hθmatch,hGeom⟩:=
    hGeom root eParent hParent (min εcap εvortex) ζh ζe γ hroot heParent hhParent hεcap' hζh hζe hγ hγParent
  have hεcapBound:ε≤εcap:=hεbound.trans (min_le_left _ _)
  have hεvBound:ε≤εvortex:=hεbound.trans (min_le_right _ _)
  refine ⟨cMatch,eCleanup,hCleanup,lam,ε,βe,βh,θmatch,
    hc,heEq,hhEq,hcCap,hβeEq,hβhEq,hβe,hβh,hlam,hrootBound,hlam1,hlamρ,hlame,hlamh,hrow,hlevel,
    hε,hεcapBound,hεvBound,hε1,hεξ,hερ,hεroot,hθeq,hθmatch,?_⟩
  intro profileCap rateCap hProfileCap hRateCap
  let rateParent:ℝ:=min (δend*ε/16) (profileCap/2)
  have hrateParent:0<rateParent:=by dsimp [rateParent];positivity
  have hrateParentCap:rateParent≤δend*ε/8:=by
    have hh:=min_le_left (δend*ε/16) (profileCap/2)
    have hp:0≤δend*ε:=mul_nonneg hδend.le hε.le
    dsimp [rateParent]
    nlinarith only [hh,hp]
  have hrateProfileCap:rateParent≤profileCap:=by
    have hh:=min_le_right (δend*ε/16) (profileCap/2)
    dsimp [rateParent]
    linarith
  obtain ⟨ζ,δDeep,rateBig,hζ,hζlimit',hζrate,hδDeep,hδα,hrateBig,hDeep⟩:=hDeep ε hε hεvBound rateParent hrateParent
  let rate:ℝ:=min rateBig (rateCap/2)
  have hrate:0<rate:=by dsimp [rate];positivity
  have hrateBigBound:rate≤rateBig:=min_le_left _ _
  have hrateCapBound:rate≤rateCap:=by
    have hh:=min_le_right rateBig (rateCap/2)
    dsimp [rate]
    linarith
  refine ⟨rateParent,ζ,δDeep,rate,hrateParent,hrateParentCap,hrateProfileCap,
    hζ,hζlimit',hζrate,hδDeep,hδα,hrate,hrateCapBound,?_⟩
  intro pcap othercap hpcap hother
  obtain ⟨ellCap,kcap,pbound,hellEq,hell,hkcap,hpbound,hpcapBound,p,εsup,finishCap,δsample,loadCap,
    hp,hpbound',hp1,hpθ,hsqrt,hεsup,hεsupCap,hfinish,hfinishOther,hfinishEll,hδsample,hload,hload1,
    hmargin,hrates,hcapacity,hGeom⟩:=hGeom rate pcap othercap hrate hpcap hother
  obtain ⟨ν,cap,hν,hcap',hνcap,hcapcap,Nfinish,hfinishNum⟩:=
    ordinary_asymmetric_finish_numeric_witness mWheel eParent hParent ε βe βh θmatch p δsample ellCap finishCap kcap rate
      hfinish hfinishEll hmargin hrates hcapacity
  refine ⟨ellCap,kcap,pbound,p,εsup,finishCap,δsample,loadCap,ν,cap,
    hellEq,hell,hkcap,hpbound,hpcapBound,hp,hpbound',hp1,hpθ,hsqrt,hεsup,hεsupCap,
    hfinish,hfinishOther,hfinishEll,hδsample,hload,hload1,hν,hcap',hνcap,hcapcap,Nfinish,hfinishNum,?_⟩
  intro ηpack hηpack
  obtain ⟨εout,γgeom,aLoad,ξroot,η₀,ηbal,ηInitial,βcap,δcap,
    hεout,hεout1,hγgeom,haLoad,haLoad1,haLoadCap,haLoadγ,haLoadEdit,hξEq,hξ,hξε,hξγ,hξload,
    hellRate,hcoverRate,hηEq,hη₀,hηbal,hηbalCap,hηbalγ,hηInitial,hηInitialCap,hβcap,hβcap1,hβcapγ,hδcap,hδcapγ,hGeom⟩:=
    hGeom ηpack hηpack
  obtain ⟨δInitial,hδInitial,hδIα,hδIη,hDeep⟩:=hDeep ηInitial aLoad ξroot η₀ ηbal
    hηInitial haLoad haLoad1 hξEq hηEq hηbal hηbalCap
  refine ⟨εout,γgeom,aLoad,ξroot,η₀,ηbal,ηInitial,βcap,δcap,δInitial,
    hεout,hεout1,hγgeom,haLoad,haLoad1,haLoadCap,haLoadγ,haLoadEdit,hξEq,hξ,hξε,hξγ,hξload,
    hellRate,hcoverRate,hηEq,hη₀,hηbal,hηbalCap,hηbalγ,hηInitial,hηInitialCap,hβcap,hβcap1,hβcapγ,
    hδcap,hδcapγ,hδInitial,hδIα,hδIη,?_⟩
  intro β hβ hβ1 hβcap hβI hβD C hC
  obtain ⟨mInitial,mBalance,mCover,hmI,hmB,hmC,hInitial,hBalance,hCover⟩:=hDeep β hβ hβ1 hβI hβD C hC
  refine ⟨mInitial,mBalance,mCover,hmI,hmB,hmC,hInitial,?_,hCover,?_⟩
  · exact ordinary_actual_trace_balance_rate_monotone ε ρ₀ α pmin hmin ηProfile ζ cBoundary δDeep rate rateBig d 2 β C mBalance hrateBigBound hBalance
  · intro εR εH pH hεR hεRcap hεH hεHcap hpH hpH1
    exact hGeom β εR εH pH hβ hβcap hεR hεRcap hεH hεHcap hpH hpH1
end Oberwolfach
