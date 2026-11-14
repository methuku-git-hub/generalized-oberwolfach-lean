module

public import Oberwolfach.OrdinaryTriangleOriginalOrderedSelectedSetup
public import Oberwolfach.OrdinaryTrianglePreHostWheelAndMatchingThresholds
public import Oberwolfach.OrdinaryTriangleFailureBudgetBeforeAbsorber

@[expose] public section
/-! From the original feasible triangle parameters, fix the edit and
correction rates before χ; after χ choose the common lookback-vortex size
and the matching/correction thresholds for those same rates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 120000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_original_presample_thresholds
    (L:ℕ) (θ α₀ εmax ρ₀ βfreq:ℝ)
    (hθhalf:1/2≤θ) (hθcycle:cycleThreshold 3≤θ) (hθ1:θ<1)
    (hα₀:0<α₀) (hεmax:0<εmax) (hρ₀:0<ρ₀) (hρ₀1:ρ₀≤1)
    (hβfreq:0<βfreq) (hβfreq1:βfreq≤1):
    ∃α:ℝ,∃hα:0<α,α≤α₀ ∧
    ∃m kMatch dMin d:ℕ,∃βPlace lamPlace ζPlace εearly capPlace capChosen ε δcap ηBudget δAbs hAbs εabs εv ξedit ξAbs:ℝ,
      0<ξedit ∧ 0<ε ∧ ε≤εmax ∧
      OrdinaryPlacementEarlyRateData (α/2) ρ₀ (βfreq/200) capPlace βPlace lamPlace ζPlace εearly dMin ∧
      OrdinaryOriginalPreSampleFixedJointRatesAt L 3 d m kMatch dMin βfreq ρ₀ α (α/2) capPlace capChosen θ
        (by omega) hβfreq hβfreq1 hρ₀ hα βPlace lamPlace ζPlace εearly ε δcap ηBudget (α/2) (ρ₀*(βfreq/200)/2) (ρ₀/4)
        δAbs hAbs εabs εv ξedit ξAbs ∧
    ∀χ:ℝ,0<χ→∃capFailure:ℝ,0<capFailure ∧ ∃Nfailure:ℕ,1≤Nfailure ∧
      OrdinaryTriangleFailureBudgetBeforeAbsorber χ capFailure Nfailure ∧
    ∃t:ℝ,0<t ∧ t≤capFailure ∧ ∃β:ℝ,0<β ∧ β≤1/4 ∧ ∃mVortex mv:ℕ,
      1≤mv ∧ mVortex≤mv ∧ OrdinaryLookbackVortexAt β ε ρ₀ d mVortex ∧
      OrdinaryOriginalPreSampleJointThresholdsSeparateListsAt L 3 d m kMatch dMin βfreq ρ₀ α (α/2) capPlace capChosen θ
        (by omega) hβfreq hβfreq1 hρ₀ hα βPlace lamPlace ζPlace εearly ε δcap ηBudget (α/2) (ρ₀*(βfreq/200)/2) (ρ₀/4)
        δAbs hAbs εabs εv mv (2*mv) 10 t t t t t t t t t t t t ξedit ξAbs β :=by
  obtain ⟨hpstar,hpstar1,α,cInner,CInner,κ,cOuter,COuter,hrefLocal,δcut,ζcut,εcut,ζlimit,εsample,εvortex,cBoundary,cInitial,εcap,eParent,hParent,
    hα,hαsub,hα1,hmargin,hc,hC,hinner,hroot,hκ,hκ1,hκcap,hcOuter,hCOuter,houter,
    hhref,hhrefcap,hδcut,hδsmall,hδcap,hζcut,hεcut,hζlimit,hεsample,hεvortex,hεvsmall,hnum,hBoundary,hInitial,hdeep,hmatch,
    hεcap,hεmax',hεvortexCap,hεκ,hερ,he,heB,heI,hh,hhB,hhI,
    δAbs,hAbs,εabs,εv,capPlace,hCorr,hPlace,hPlaceCap,hAbsCap,hVCap,m,kMatch,βPlace,lamPlace,ζPlace,εearly,dMin,
    hearly,hearlyCap,hAt,hEarly,hTail,hReference⟩:=
      ordinary_triangle_original_ordered_selected_setup L θ α₀ εmax ρ₀ βfreq hθhalf hθcycle hθ1 hα₀ hεmax hρ₀ hρ₀1 hβfreq hβfreq1
  obtain ⟨δref,href,βP,hδref,hδrefSmall,hhrefRef,hβP,kParent,βH,cParent,Bparent,hkParent,hβH,hcParent,hBparent,hselection,
    εstar,cLinear,εf,ηhub,ηend,ζfresh,εrows,hεstar,hlinear,hεf,hηhub,hηend,hζfresh,hrows,hrowsGeom,hfamily,
    ηH,gapRoot,ζroot,rateRoot,lamRoot,hηH,hgapRoot,hfit,hζroot,hζcap,hrateRoot,hlamRoot,N₀,hN₀,hscale,hrefRoot,
    lamFine,hlamFine,hfine,ξGeo,ζGeo,edit,hξGeo,hζGeo,hedit,hξcap,hζgeocap,hξζ,hpack,
    lam,ε,βe,βh,θmatch,ellCap,hVortex,hlamFineBound,
    ξInner,Kdom,BInner,tHub,eEvent,hEvent,capInner,γold,κold,δInner,tpot,lamInner,bold,Bold,βcap,hselected,hchoice⟩:=hReference
  have hε:0<ε:=hVortex.1
  have hεearly:ε≤εearly:=hVortex.2.1
  have hεmax:ε≤εmax:=hεearly.trans (hearlyCap.trans (hPlaceCap.trans hεmax'))
  have hεearlyκ:εearly≤κ:=hearlyCap.trans (hPlaceCap.trans hεκ)
  have hεearlyρ:εearly≤ρ₀/16:=hearlyCap.trans (hPlaceCap.trans hερ)
  have hεearlyVortex:εearly≤εvortex:=hearlyCap.trans (hPlaceCap.trans hεvortexCap)
  have hm:7≤m:=hAt.2.1
  obtain ⟨rateParent,ζcert,δDeep,rate,hrate,hrateRoot,hrateInner,hrateEnd,hscale',hζ,hζrate,hζcap,hζlimit',
    hδDeep,hδα,hrateDeep,p,εsup,capSmall,δsample,ν,hp,hp1,hpθ,hsqrt,hεsup,hεsupCap,hcapSmall,hcapOther,hcapEll,
    hδsample,hν,hνcap,Norder,hNorder,τcover,hτeq,hτ,hτcap,hτ1,hsafe1,hsafe2,hsafe3,hfinish,hbudgetE,hbudgetH,
    eps,γgeo,aLoad,ξroot,η₀,ηbal,ηInitial,heps,heps1,hγ,hgeometry,hcover,ha,ha1,hacapSmall,haκ,haγ,haedit,hξeq,hξ,hξγ,hξcap,
    hηeq,hη₀,hη,hη₀cap,hηγ,hηI,hηIcap,hsmall,hsmall',hellBound,δInitial,hδInitial,hδIα,hδIη,hcallbacks,
    δedit,ηedit,ηBudget,capChosen,hδedit,hδαedit,hδbal,hηedit,hBudget,hBudgetη,hsmallBudget,hChosen,hChosen1,hChosenBudget,
    d,hd,hmargins,bHub,Bweight,ξdeep,tOuter,ζouter,δOuter,δcap,rateOuter,ξedit,ξAbs,
    hb,hbc,hB,hBbound,hξdeep,hξdeepcap,hβchoose,htOuter,hζouter,hζlimitOuter,hδOuter,hδαOuter,hδcap,hδζ,hrateOuter,htrace,houterChoice,hjoint,hAfterLosses⟩:=
    ordinary_triangle_pre_host_wheel_and_matching_thresholds (α/2) ρ₀ (ρ₀*(βfreq/200)/2) cInner CInner ηhub eParent hParent (ρ₀/8) ηend εf εrows 1
      ξInner Kdom BInner tHub eEvent hEvent capInner γold κold δInner tpot lamInner bold Bold βcap ε 1 cBoundary
      hselected hdeep (by norm_num) βH ηH Bparent (ρ₀/16) (βH/2) (2*ηH) ζroot rateRoot N₀ hN₀ hrateRoot hscale ζlimit hζlimit
      kParent (βH/8) (cParent*(1-2*δref)^2) (Bparent/((ρ₀/16)*(ρ₀*(βfreq/200)/2)^(2*3-1))) (href/4) δref εstar cLinear ζfresh
      (βH/4) (2*ηH+gapRoot) (εstar-(2*ηH+gapRoot)) ξGeo ζGeo edit
      (min ((ρ₀*(βfreq/200)/2)^4/32) (endpointCountCoefficient (ρ₀*(βfreq/200)/2) (ρ₀/8)/4)/4)
      βe βh ellCap lam lamRoot δcut εearly θmatch κ hVortex hchoice hρ₀ hδcut hedit hκ (by positivity) hpstar hεearlyκ hεearlyρ
      cOuter COuter cInitial hcOuter hCOuter houter hmatch L m kMatch dMin βfreq α (α/2) capPlace θ
      hβfreq hβfreq1 hα βPlace lamPlace ζPlace εearly hTail δAbs hAbs εabs εv hCorr rfl rfl hζfresh εsample hεsample
      βP 1 cParent (2*δref) href (by omega) hηH hselection
      hrefLocal ζcut εcut εvortex (min ((α/2)/4) (1/4:ℝ)) hnum hδsmall hεearlyVortex hξGeo hζcut.le hεcut.le hδcap hhrefcap
      hρ₀1 hθhalf hm le_rfl (hearlyCap.trans hAbsCap) (hearlyCap.trans hVCap) hEarly
  have hjointKeep:=hjoint
  obtain ⟨δ,θmatch',κplace,bplace,zplace,matchErr,σbal,κprime,dNeed,hStage,βSel,lamSel,ζSel,smin,K,rank,hSpacing,
    ζret,Nplace,lamMatch,aRow,γrow,BO,hPlacementAfter,hMatching,hBO,hd',hSelect,τmatch,tMatch,ξMatch,bMatch,hChoice,hColumns,
    hξedit,hξeditCap,hξeditBudget,hξeditσ,hξeditList,hξeditMatch,hColumnsAt,hξAbs,hξAbsCap,hξAbsBudget,hξAbsσ,hξAbsh,hCorrection⟩:=hjoint
  refine ⟨α,hα,hαsub,m,kMatch,dMin,d,βPlace,lamPlace,ζPlace,εearly,capPlace,capChosen,ε,δcap,ηBudget,δAbs,hAbs,εabs,εv,ξedit,ξAbs,
    hξedit,hε,hεmax,hEarly,hjointKeep,?_⟩
  intro χ hχ
  obtain ⟨capFailure,hcapFailure,Nfailure,hNfailure,hfailure⟩:=ordinary_triangle_failure_budget_before_absorber χ hχ
  let t:ℝ:=capFailure/2
  have ht:0<t:=by dsimp [t];positivity
  have htCap:t≤capFailure:=by dsimp [t];linarith
  obtain ⟨βsmall,r,hβsmall,hβold,hr,hrI,hrD,hrE,hrS,hrG,hrEnd,hrRows,hselected',
    εTri,β,hεTri,hβ,hβone,hβα8,hβα4,hβκ,hβcap,hβδ,hβtri,hβcert,hβI,hβD,hβE,hβG,hgapOuter,hgapInner,hβbalance,
    v₀,Mhost,Mcut,hv₀,hMhost,hMcut,hafter,hselector,hcuts,vInner,hvInner,hInner,
    Msmall,vCert,vCommon,hMsmall,hvCert,hvouter,hvinner,hvcert,hcert,
    mInitial,mBalance,mEdit,Nedit,mFineInitial,mFineLater,mGeom,mAll,hmI,hmB,hmEdit,hmGeom,hI,hB',hE',hFI,hFL,hG,
    hInitAt,hBalance,hMargins,hFine,hLater,hGeom,M,vCommon',mVortex,mv,hM,hSmall,hN₀',hNcert,hNedit,htwo,hmatchBound,hvCert',hvOuter,hvInner',hmAll,
    hmv,hCommon,hVortexSize,hterm,hhostSize,hcutSize,hlook,hcert',hThresholds⟩:=
      hAfterLosses t t t t t t t t t ht ht ht ht ht ht ht ht ht
  refine ⟨capFailure,hcapFailure,Nfailure,hNfailure,hfailure,t,ht,htCap,β,hβ,hβone,mVortex,mv,hmv,hVortexSize,hlook,?_⟩
  exact hThresholds t t t t t t t t t t t t ht ht ht ht ht ht ht ht ht ht ht ht
end Oberwolfach
