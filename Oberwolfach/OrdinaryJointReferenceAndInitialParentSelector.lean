module

public import Oberwolfach.OrdinaryJointGeometryCertificateSharedInitialParentEarlyK
public import Oberwolfach.OrdinaryGeneralDeepReferenceCapacityHierarchyLinearMin

@[expose] public section
/-! Select one reference wheel size while retaining the initial scaled
profile, compatible parent margins and later certificate choices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 80000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinarySharedInitialParentJointSelectorAt
    (mWheel loadK d:ℕ) (hm:3≤mWheel) (α:ℝ) (k:ℕ):Prop:=
    ∀(ρ₀ hmin href δlimit a ρ θ pmin ηProfile:ℝ)
    (βparent b B εparent gap geomCap:ℝ)
    (hρ₀:0<ρ₀) (hhmin:0<hmin) (hhref:0<href) (hδlimit:0<δlimit)
    (ha:0<a) (hρ:0<ρ) (hθ:0<θ) (hpmin:0<pmin) (hηProfile:0<ηProfile)
    (hβparent:0<βparent) (hb:0<b) (hB:0≤B) (hgap:0<gap) (hcap:0<geomCap),
    ∃δcut ζcut εcut ζlimit εsample εvortex cBoundary βout ξreserve ζout edit:ℝ,
      0<δcut ∧ δcut<1/4 ∧ δcut≤δlimit ∧ 0<ζcut ∧ 0<εcut ∧ 0<ζlimit ∧
      0<εsample ∧ 0<εvortex ∧ εvortex<1/4 ∧ 0<cBoundary ∧
      OrdinaryFixedVortexNonrootNumericAt ρ₀ hmin href a ρ θ δcut ζcut εcut ζlimit εsample εvortex ∧
      ∃cProfile:ℝ,0<cProfile ∧ OrdinaryInitialSharpReferenceScaledProfileAt mWheel loadK d hm ρ₀ α pmin δcut cProfile ∧
      0<βout ∧ βout=βparent/2 ∧ 0<ξreserve ∧ 0<ζout ∧ 0<edit ∧ ξreserve≤geomCap ∧ ζout≤geomCap ∧
    ∃γ eParent hParent:ℝ,0<γ ∧ 0<eParent ∧ 0<hParent ∧ γ≤eParent ∧
      eParent≤cBoundary ∧ hParent≤cBoundary ∧ eParent≤cProfile ∧ hParent≤cProfile ∧
    ∀ω bRoot BRoot hpack δ:ℝ,0<ω→0<bRoot→0<BRoot→0<hpack→0<δ→δ<1/4→
    ∃εstar cLinear:ℝ,0<εstar ∧ 0<cLinear ∧
    ∀bHub BHub p₀ κ:ℝ,0<bHub→0≤BHub→0<p₀→p₀≤1→0<κ→κ≤1→
    ∃ηhub ζhub aEnd ηend ζlocal δend:ℝ,
      0<ηhub ∧ 0<ζhub ∧ 0<aEnd ∧ aEnd≤1 ∧ 0<ηend ∧ 0<ζlocal ∧ 0<δend ∧
    ∀root εcap:ℝ,0<root→0<εcap→
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
    ∃n₀ Nclean:ℕ,∃εout γgeom aLoad ξroot η₀ ηbal ηInitial βcap δcap δInitial:ℝ,
      0<εout ∧ εout≤1 ∧ 0<γgeom ∧ 0<aLoad ∧ aLoad≤1 ∧ aLoad≤loadCap ∧ aLoad≤γgeom/1000 ∧
      aLoad≤edit/(72*((mWheel:ℝ)+2)) ∧ ξroot=min (ε/200) (aLoad^2/160) ∧
      0<ξroot ∧ ξroot≤ε/100 ∧ ξroot≤γgeom/160000 ∧ 80*ξroot≤aLoad^2 ∧
      max (18*aLoad+3*(((loadK:ℝ)+1)*lam)) ((3*aLoad+lam)*((mWheel:ℝ)+1))≤ellCap ∧ 10*ξroot≤finishCap ∧
      η₀=δcut*(ρ₀/8)*ξroot/1000 ∧ 0<η₀ ∧ 0<ηbal ∧ ηbal≤η₀ ∧ ηbal≤γgeom/1000 ∧
      0<ηInitial ∧ ηInitial≤ηbal ∧ 0<βcap ∧ βcap≤1/4 ∧ βcap≤γgeom/1000 ∧
      0<δcap ∧ δcap≤γgeom/1000 ∧ 0<δInitial ∧ δInitial≤α ∧ δInitial≤ηInitial ∧
    ∃Nreserve Ncert:ℕ,
      OrdinaryVortexFineCertificateAtGeneralLoad {m:=mWheel, k:=k, loadK:=loadK, hm:=hm, α:=α, ω:=ω, β:=βout, bRoot:=bRoot, BRoot:=BRoot, hpack:=hpack, δ:=δ, εstar:=εstar, ηpack:=ηpack, γ:=γ, bHub:=bHub, BHub:=BHub, p₀:=p₀, κ:=κ, ηhub:=ηhub, ζhub:=ζhub, ζlocal:=ζlocal, δend:=δend, b₀:=2*(3*d), p:=p, βe:=βe, βh:=βh, ν:=ν, cap:=cap, εsup:=εsup, δsample:=δsample, τ:=τ, L:=((2*(3*d):ℕ):ℝ), n₀:=n₀, Nclean:=Nclean, εgeom:=εout, Nreserve:=Nreserve, Ncert:=Ncert} ∧
    ∀β:ℝ,0≤β→β≤1/4→β≤βcap→β≤δInitial→β≤δDeep→∀C:ℝ,0≤C→
    ∃mInitial mBalance mCover:ℕ,1≤mInitial ∧ 1≤mBalance ∧ 1≤mCover ∧
      OrdinaryVortexInitialAmbientBalanceAt ε ρ₀ α pmin hmin ηInitial cBoundary δInitial d β mInitial ∧
      OrdinaryDeepTraceSeparatedBalanceAt ε ρ₀ α pmin hmin ηProfile ζ cBoundary δDeep rate d 2 β C mBalance ∧
      OrdinaryDeepTraceFineCoverAtLocalBalance mWheel loadK 2 ρ₀ hmin href δcut ζcut εcut ζlimit εsample ε ξroot aLoad a ρ θ β ηbal d mCover ∧
    ∀εR εH pH:ℝ,0≤εR→εR≤δcap→0≤εH→εH≤δcap→0≤pH→pH≤1→
      OrdinaryVortexTwoStepSharpGeometryAtRatesGeneralLoad mWheel loadK d k β ε ρ₀ lam ξreserve ξroot aLoad ηbal ηInitial γgeom edit p βe βh pH εR εH
        βparent b B εparent gap βout ζout ηpack εout

theorem ordinary_joint_reference_and_initial_parent_selector
    (m loadK d:ℕ) (hm:3≤m) (hd:2≤d) (α ρ₀ pstar ηP:ℝ)
    (hα:0<α) (hα1:α≤1/2)
    (hθ1:max (1/2) (cycleThreshold (m+1))+α/2≤1)
    (hρ₀:0<ρ₀) (hp:0<pstar) (hp1:pstar≤1) (hηP:0<ηP):
    ∃(δ h βP row:ℝ) (k:ℕ) (βH c B εstar cLinear:ℝ),
      0<δ ∧ δ<1/4 ∧ 0<h ∧ 0<βP ∧ 0<row ∧ m+3≤k ∧
      0<βH ∧ 0<c ∧ 0<B ∧ 0<εstar ∧ 0<cLinear ∧
      OrdinaryGeneralDeepSafeCapacityRuleLinear m k hm α (ρ₀/16) (βH/8)
        (c*(1-δ)^((m+1)-1)) (B/((ρ₀/16)*pstar^(2*(m+1)-1))) (h/2) (δ/2) εstar cLinear ∧
      OrdinarySharedInitialParentJointSelectorAt m loadK d hm α k ∧
    ∀(ηH ε χhost χcut:ℝ),0<ηH→0<ε→ε<1→0<χhost→0<χcut→
    ∃εTri βmax:ℝ,0<εTri ∧ 0<βmax ∧ βmax≤1/4 ∧ βmax≤α/4 ∧ βmax≤εTri ∧
    ∃Mhost Mcut:ℕ,1≤Mhost ∧ 1≤Mcut ∧
      OrdinaryGeneralFixedDomainSelector m k d Mhost hm hd (max (1/2) (cycleThreshold (m+1))) α pstar (ρ₀/16)
        βP ηP row ηH βH c B εTri ε χhost (2*(3*d)) hp ∧
      OrdinaryReferenceCutsDomainSelector d Mcut hd α pstar (ρ₀/16) δ h ε χcut (2*(3*d)) :=by
  obtain ⟨Nroot,hjoint⟩:=ordinary_joint_geometry_certificate_shared_initial_parent_early_k m loadK d hm α hα
  obtain ⟨δ,h,βP,row,k,βH,c,B,εstar,cLinear,hδ,hδ1,hh,hβP,hrow,hk,hkmin,hβH,hc,hB,hεstar,hcLinear,hrule,hevents⟩:=
    ordinary_general_deep_reference_capacity_hierarchy_linear_min Nroot m d hm hd α ρ₀ pstar ηP hα hα1 hθ1 hρ₀ hp hp1 hηP
  have hk4:4≤k:=by omega
  exact ⟨δ,h,βP,row,k,βH,c,B,εstar,cLinear,hδ,hδ1,hh,hβP,hrow,hk,hβH,hc,hB,hεstar,hcLinear,
    hrule,hjoint k hkmin hk4,hevents⟩
end Oberwolfach
