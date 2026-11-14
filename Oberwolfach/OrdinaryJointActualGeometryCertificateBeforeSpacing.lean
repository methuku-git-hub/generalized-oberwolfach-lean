module

public import Oberwolfach.OrdinaryActualInitialDeepSampledSharedNumericLocalHostBeforeSpacing
public import Oberwolfach.OrdinaryVortexFineCertificatePackagedBeforeConflict
public import Oberwolfach.OrdinaryInitialDeepFineSeparatedOrder
public import Oberwolfach.OrdinaryAsymmetricGeometryParentMarginHierarchy
public import Oberwolfach.OrdinaryAsymmetricFinishNumericWitness

@[expose] public section
/-! Select the profile cost rate before the fresh-sampling probability,
then align the later fine cover, initial balance and root geometry choices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 80000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_joint_actual_geometry_certificate_before_spacing
    (mWheel loadK:ℕ) (hm:3≤mWheel) (α:ℝ) (hα:0<α):
    ∃Nroot:ℕ,∀k:ℕ,Nroot≤k→4≤k→
    ∀(ρ₀ hmin href δlimit a ρ θ pmin ηProfile:ℝ)
    (βparent b B εparent gap geomCap:ℝ)
    (hρ₀:0<ρ₀) (hhmin:0<hmin) (hhref:0<href) (hδlimit:0<δlimit)
    (ha:0<a) (hρ:0<ρ) (hθ:0<θ) (hpmin:0<pmin) (hηProfile:0<ηProfile)
    (hβparent:0<βparent) (hb:0<b) (hB:0≤B) (hgap:0<gap) (hcap:0<geomCap),
    ∃δcut ζcut εcut ζlimit εsample εvortex cBoundary βout ξreserve ζout edit:ℝ,
      0<δcut ∧ δcut<1/4 ∧ δcut≤δlimit ∧ 0<ζcut ∧ 0<εcut ∧ 0<ζlimit ∧
      0<εsample ∧ 0<εvortex ∧ εvortex<1/4 ∧ 0<cBoundary ∧
      OrdinaryFixedVortexNonrootNumericAt ρ₀ hmin href a ρ θ δcut ζcut εcut ζlimit εsample εvortex ∧
      0<βout ∧ βout=βparent/2 ∧ 0<ξreserve ∧ 0<ζout ∧ 0<edit ∧ ξreserve≤geomCap ∧ ζout≤geomCap ∧
    ∀ω bRoot BRoot hpack δ:ℝ,0<ω→0<bRoot→0<BRoot→0<hpack→0<δ→δ<1/4→
    ∃εstar cLinear:ℝ,0<εstar ∧ 0<cLinear ∧
    ∀γ bHub BHub p₀ κ:ℝ,0<γ→0<bHub→0≤BHub→0<p₀→p₀≤1→0<κ→κ≤1→
    ∃ηhub ζhub aEnd ηend ζlocal δend:ℝ,
      0<ηhub ∧ 0<ζhub ∧ 0<aEnd ∧ aEnd≤1 ∧ 0<ηend ∧ 0<ζlocal ∧ 0<δend ∧
    ∀root eParent hParent εcap:ℝ,
      0<root→0<eParent→0<hParent→0<εcap→γ≤eParent→
      eParent≤cBoundary→hParent≤cBoundary→
    ∃cMatch eCleanup hCleanup lam ε βe βh θmatch:ℝ,
      0<cMatch ∧ eCleanup=eParent/2 ∧ hCleanup=hParent/2 ∧
      cMatch≤min (ζhub*γ*(1/4:ℝ)) (ζlocal*(1/4:ℝ))/2 ∧
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
    ∃τ ηpack:ℝ,τ=ordinarySafeCleanupScale (mWheel+1) p βe (βh/2) ν (min cap 1) ∧
      0<τ ∧ τ≤cap ∧ τ≤1 ∧ 0<ηpack ∧ cLinear*τ≤ηpack ∧
    ∃n₀:ℕ,∃εout γgeom aLoad ξroot η₀ ηbal ηInitial βcap δcap δInitial:ℝ,
      0<εout ∧ εout≤1 ∧ 0<γgeom ∧ 0<aLoad ∧ aLoad≤1 ∧ aLoad≤loadCap ∧ aLoad≤γgeom/1000 ∧
      aLoad≤edit/(72*((mWheel:ℝ)+2)) ∧ ξroot=min (ε/200) (aLoad^2/160) ∧
      0<ξroot ∧ ξroot≤ε/100 ∧ ξroot≤γgeom/160000 ∧ 80*ξroot≤aLoad^2 ∧
      max (18*aLoad+3*(((loadK:ℝ)+1)*lam)) ((3*aLoad+lam)*((mWheel:ℝ)+1))≤ellCap ∧ 10*ξroot≤finishCap ∧
      η₀=δcut*(ρ₀/8)*ξroot/1000 ∧ 0<η₀ ∧ 0<ηbal ∧ ηbal≤η₀ ∧ ηbal≤γgeom/1000 ∧
      0<ηInitial ∧ ηInitial≤ηbal ∧ 0<βcap ∧ βcap≤1/4 ∧ βcap≤γgeom/1000 ∧
      0<δcap ∧ δcap≤γgeom/1000 ∧ 0<δInitial ∧ δInitial≤α ∧ δInitial≤ηInitial ∧
    ∀(d:ℕ),∃Nclean Nreserve Ncert:ℕ,
      OrdinaryVortexFineCertificateAtGeneralLoad {m:=mWheel, k:=k, loadK:=loadK, hm:=hm, α:=α, ω:=ω, β:=βout, bRoot:=bRoot, BRoot:=BRoot, hpack:=hpack, δ:=δ, εstar:=εstar, ηpack:=ηpack, γ:=γ, bHub:=bHub, BHub:=BHub, p₀:=p₀, κ:=κ, ηhub:=ηhub, ζhub:=ζhub, ζlocal:=ζlocal, δend:=δend, b₀:=2*(3*d), p:=p, βe:=βe, βh:=βh, ν:=ν, cap:=cap, εsup:=εsup, δsample:=δsample, τ:=τ, L:=((2*(3*d):ℕ):ℝ), n₀:=n₀, Nclean:=Nclean, εgeom:=εout, Nreserve:=Nreserve, Ncert:=Ncert} ∧
    ∀β:ℝ,0≤β→β≤1/4→β≤βcap→β≤δInitial→β≤δDeep→∀C:ℝ,0≤C→
    ∃mInitial mBalance mCover:ℕ,1≤mInitial ∧ 1≤mBalance ∧ 1≤mCover ∧
      OrdinaryVortexActualInitialAmbientBalanceAt ε ρ₀ α pmin hmin ηInitial cBoundary δInitial d β mInitial ∧
      OrdinaryActualTraceSeparatedBalanceAt ε ρ₀ α pmin hmin ηProfile ζ cBoundary δDeep rate d 2 β C mBalance ∧
      OrdinaryActualTraceFineCoverAtLocalBalanceLocalHost mWheel loadK 2 ρ₀ hmin href δcut ζcut εcut ζlimit εsample ε ξroot aLoad a ρ θ β ηbal d mCover ∧
    ∀εR εH pH:ℝ,0≤εR→εR≤δcap→0≤εH→εH≤δcap→0≤pH→pH≤1→
      OrdinaryVortexTwoStepSharpGeometryAtRatesGeneralLoad mWheel loadK d k β ε ρ₀ lam ξreserve ξroot aLoad ηbal ηInitial γgeom edit p βe βh pH εR εH
        βparent b B εparent gap βout ζout ηpack εout :=by
  obtain ⟨Nroot,hCert⟩:=ordinary_vortex_fine_certificate_packaged_before_conflict mWheel loadK hm α hα
  refine ⟨Nroot,?_⟩
  intro k hkN hk ρ₀ hmin href δlimit a ρ θ pmin ηProfile βparent b B εparent gap geomCap
    hρ₀ hhmin hhref hδlimit ha hρ hθ hpmin hηProfile hβparent hb hB hgap hcap
  obtain ⟨δcut,ζcut,εcut,ζlimit,εsample,εvortex,cBoundary,βout,ξreserve,ζout,edit,
    hδcut,hδcut1,hδlimit',hζcut,hεcut,hζlimit,hεsample,hεvortex,hεvortex1,hcBoundary,hNumeric,
    hβout,hβeq,hξreserve,hζout,hedit,hξcap,hζcap,hGeom⟩:=
    ordinary_actual_initial_deep_sampled_shared_numeric_local_host_before_spacing mWheel loadK k hm hk
      ρ₀ hmin href δlimit a ρ θ α pmin ηProfile βparent b B εparent gap geomCap
      hρ₀ hhmin hhref hδlimit ha hρ hθ hα hpmin hηProfile hβparent hb hB hgap hcap
  refine ⟨δcut,ζcut,εcut,ζlimit,εsample,εvortex,cBoundary,βout,ξreserve,ζout,edit,
    hδcut,hδcut1,hδlimit',hζcut,hεcut,hζlimit,hεsample,hεvortex,hεvortex1,hcBoundary,hNumeric,
    hβout,hβeq,hξreserve,hζout,hedit,hξcap,hζcap,?_⟩
  intro ω bRoot BRoot hpack δ hω hbRoot hBRoot hhpack hδ hδ1
  obtain ⟨εstar,cLinear,hεstar,hcLinear,hCert⟩:=hCert k hkN ω βout bRoot BRoot hpack δ
    hω hβout hbRoot hBRoot hhpack hδ hδ1
  refine ⟨εstar,cLinear,hεstar,hcLinear,?_⟩
  intro γ bHub BHub p₀ κ hγ hbHub hBHub hp₀ hp₀1 hκ hκ1
  obtain ⟨ηhub,ζhub,aEnd,ηend,ζlocal,δend,hηhub,hζhub,haEnd,haEnd1,hηend,hζlocal,hδend,hCert⟩:=
    hCert γ bHub BHub p₀ κ hγ hbHub hBHub hp₀ hp₀1 hκ hκ1
  refine ⟨ηhub,ζhub,aEnd,ηend,ζlocal,δend,hηhub,hζhub,haEnd,haEnd1,hηend,hζlocal,hδend,?_⟩
  intro root eParent hParent εcap hroot heParent hhParent hεcap hγParent heBound hhBound
  obtain ⟨cMatch,eCleanup,hCleanup,lam,ε,βe,βh,θmatch,
    hc,heEq,hhEq,hcCap,hβeEq,hβhEq,hβe,hβh,hlam,hrootBound,hlam1,hlamρ,hlame,hlamh,hrow,hlevel,
    hε,hεcapBound,hεvBound,hε1,hεξ,hερ,hεroot,hθeq,hθmatch,hGeom⟩:=
    hGeom root eParent hParent εcap ζhub ζlocal γ δend hroot heParent hhParent hεcap hζhub hζlocal hγ hγParent hδend heBound hhBound
  refine ⟨cMatch,eCleanup,hCleanup,lam,ε,βe,βh,θmatch,
    hc,heEq,hhEq,hcCap,hβeEq,hβhEq,hβe,hβh,hlam,hrootBound,hlam1,hlamρ,hlame,hlamh,hrow,hlevel,
    hε,hεcapBound,hεvBound,hε1,hεξ,hερ,hεroot,hθeq,hθmatch,?_⟩
  intro profileCap rateCap hProfileCap hRateCap
  obtain ⟨rateParent,ζ,δDeep,rate,hrateParent,hrateParentCap,hrateProfileCap,
    hζ,hζlimit',hζrate,hδDeep,hδα,hrate,hrateCap,hGeom⟩:=hGeom profileCap rateCap hProfileCap hRateCap
  refine ⟨rateParent,ζ,δDeep,rate,hrateParent,hrateParentCap,hrateProfileCap,
    hζ,hζlimit',hζrate,hδDeep,hδα,hrate,hrateCap,?_⟩
  intro pcap othercap hpcap hother
  obtain ⟨ellCap,kcap,pbound,p,εsup,finishCap,δsample,loadCap,ν,cap,
    hellEq,hell,hkcap,hpbound,hpcapBound,hp,hpbound',hp1,hpθ,hsqrt,hεsup,hεsupCap,
    hfinish,hfinishOther,hfinishEll,hδsample,hload,hload1,hν,hcap',hνcap,hcapcap,Nfinish,hfinishNum,hGeom⟩:=
    hGeom pcap othercap hpcap hother
  refine ⟨ellCap,kcap,pbound,p,εsup,finishCap,δsample,loadCap,ν,cap,
    hellEq,hell,hkcap,hpbound,hpcapBound,hp,hpbound',hp1,hpθ,hsqrt,hεsup,hεsupCap,
    hfinish,hfinishOther,hfinishEll,hδsample,hload,hload1,hν,hcap',hνcap,hcapcap,Nfinish,hfinishNum,?_⟩
  obtain ⟨τ,hτeq,hτ,hτcap,hτ1,ηpack,hηpack,hlinear,n₀,hCert⟩:=hCert p βe βh ν cap εsup δsample
    hp hp1 hβe hβh hν hcap' hεsup hδsample
  refine ⟨τ,ηpack,hτeq,hτ,hτcap,hτ1,hηpack,hlinear,n₀,?_⟩
  obtain ⟨εout,γgeom,aLoad,ξroot,η₀,ηbal,ηInitial,βcap,δcap,δInitial,
    hεout,hεout1,hγgeom,haLoad,haLoad1,haLoadCap,haLoadγ,haLoadEdit,hξEq,hξ,hξε,hξγ,hξload,
    hellRate,hcoverRate,hηEq,hη₀,hηbal,hηbalCap,hηbalγ,hηInitial,hηInitialCap,hβcap,hβcap1,hβcapγ,
    hδcap,hδcapγ,hδInitial,hδIα,hδIη,hGeom⟩:=hGeom ηpack hηpack
  refine ⟨εout,γgeom,aLoad,ξroot,η₀,ηbal,ηInitial,βcap,δcap,δInitial,
    hεout,hεout1,hγgeom,haLoad,haLoad1,haLoadCap,haLoadγ,haLoadEdit,hξEq,hξ,hξε,hξγ,hξload,
    hellRate,hcoverRate,hηEq,hη₀,hηbal,hηbalCap,hηbalγ,hηInitial,hηInitialCap,hβcap,hβcap1,hβcapγ,
    hδcap,hδcapγ,hδInitial,hδIα,hδIη,?_⟩
  intro d
  obtain ⟨Nclean,hCert⟩:=hCert (2*(3*d)) (((2*(3*d):ℕ):ℝ)) (by positivity)
  obtain ⟨Nreserve,Ncert,hCertAt⟩:=hCert εout hεout
  exact ⟨Nclean,Nreserve,Ncert,hCertAt,hGeom d⟩
end Oberwolfach
