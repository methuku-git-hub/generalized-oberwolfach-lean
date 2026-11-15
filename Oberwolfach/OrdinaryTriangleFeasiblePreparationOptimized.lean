module

public import Oberwolfach.OrdinaryTriangleOriginalOrderedSelectedSetup
public import Oberwolfach.OrdinaryTrianglePreHostWheelAndMatchingThresholds
public import Oberwolfach.OrdinaryTriangleFailureBudgetBeforeAbsorber
public import Oberwolfach.OrdinaryTriangleSameSampleEventToPreparation
public import Oberwolfach.OrdinaryTriangleAssignedWheelCallbackOnCommonOutcome
public import Oberwolfach.FirstVortexHubCardinality

@[expose] public section
/-! Unchecked draft: triangle branch of protected preparation, retaining the original
quantifier order and the matching, correction and wheel certificates on one
assigned sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 150000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_feasible_preparation_optimized
    (θ α₀ εmax ρ₀ βfreq:ℝ)
    (hθhalf:1/2≤θ) (hθcycle:cycleThreshold 3≤θ) (hθ1:θ<1)
    (hα₀:0<α₀) (hεmax:0<εmax) (hρ₀:0<ρ₀) (hρ₀1:ρ₀≤1)
    (hβfreq:0<βfreq) (hβfreq1:βfreq≤1):
    ∃ξ:ℝ,0<ξ ∧ ∀χ:ℝ,0<χ→χ<1→∃B N:ℕ,1≤B ∧ 1≤N ∧
    ∀n≥N,∀(P:SimpleGraph (Fin n)) (D q:ℕ),
      P.IsRegularOfDegree D→Even D→(θ+α₀)*(n:ℝ)≤D→
    let ρ:ℝ:=2*(q:ℝ)/(D:ℝ);
    ∀(hρlo:ρ₀≤ρ) (hρhi:ρ≤1),∀F:Fin q→SimpleGraph (Fin n),
      (∀u,(F u).IsRegularOfDegree 2)→
      (∀u v,cycleThreshold (Fintype.card ((F u).connectedComponentMk v))≤θ)→
      (∀u,βfreq*n≤((Finset.univ.filter (fun v=>Fintype.card ((F u).connectedComponentMk v)=3)).card:ℝ))→
    ∃I:Finset (Fin n),(I.card:ℝ)≤εmax*n ∧
      1-χ-1/(n:ℝ)^10≤(FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.retentionCoin ρ
        (hρ₀.le.trans hρlo) hρhi)).probability
        (fun σ=>ProtectedFactorPreparation P (retainedGraph P σ) I ξ B F)
 :=by
  let L:ℕ:=1
  obtain ⟨hpstar,hpstar1,α,cInner,CInner,κ,cOuter,COuter,hrefLocal,δcut,ζcut,εcut,ζlimit,εsample,εvortex,cBoundary,cInitial,εcap,eParent,hParent,
    hα,hαsub,hα1,hmargin,hc,hC,hinner,hroot,hκ,hκ1,hκcap,hcOuter,hCOuter,houter,
    hhref,hhrefcap,hδcut,hδsmall,hδcutBound,hζcut,hεcut,hζlimit,hεsample,hεvortex,hεvsmall,hnum,hBoundary,hInitial,hdeep,hmatch,
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
  have hVortexKeep:=hVortex
  obtain ⟨_,_,hεsmall,hεξV,hερV,hlamEq,hlamPos,hlamRootV,hlam1,hlamρ,hβePos,hβhPos,hlamE,hlamH,hrow,hlevel,hθmatchPos,hEllEq,hEllPos,hEllBound,hEllUpper⟩:=hVortex
  have hεmax:ε≤εmax:=hεearly.trans (hearlyCap.trans (hPlaceCap.trans hεmax'))
  have hεearlyκ:εearly≤κ:=hearlyCap.trans (hPlaceCap.trans hεκ)
  have hεearlyρ:εearly≤ρ₀/16:=hearlyCap.trans (hPlaceCap.trans hερ)
  have hεearlyVortex:εearly≤εvortex:=hearlyCap.trans (hPlaceCap.trans hεvortexCap)
  have hm:7≤m:=hAt.2.1
  have hPreHostChunks :=
    ordinary_triangle_pre_host_wheel_and_matching_thresholds (α/2) ρ₀ (ρ₀*(βfreq/200)/2) cInner CInner ηhub eParent hParent (ρ₀/8) ηend εf εrows 1
      ξInner Kdom BInner tHub eEvent hEvent capInner γold κold δInner tpot lamInner bold Bold βcap ε 1 cBoundary
      hselected hdeep (by norm_num) βH ηH Bparent (ρ₀/16) (βH/2) (2*ηH) ζroot rateRoot N₀ hN₀ hrateRoot hscale ζlimit hζlimit
      kParent (βH/8) (cParent*(1-2*δref)^2) (Bparent/((ρ₀/16)*(ρ₀*(βfreq/200)/2)^(2*3-1))) (href/4) δref εstar cLinear ζfresh
      (βH/4) (2*ηH+gapRoot) (εstar-(2*ηH+gapRoot)) ξGeo ζGeo edit
      (min ((ρ₀*(βfreq/200)/2)^4/32) (endpointCountCoefficient (ρ₀*(βfreq/200)/2) (ρ₀/8)/4)/4)
      βe βh ellCap lam lamRoot δcut εearly θmatch κ hVortexKeep hchoice hρ₀ hδcut hedit hκ (by positivity) hpstar hεearlyκ hεearlyρ
      cOuter COuter cInitial hcOuter hCOuter houter hmatch L m kMatch dMin βfreq α (α/2) capPlace θ
      hβfreq hβfreq1 hα βPlace lamPlace ζPlace εearly hTail δAbs hAbs εabs εv hCorr rfl rfl hζfresh εsample hεsample
      βP 1 cParent (2*δref) href (by omega) hηH hselection
      hrefLocal ζcut εcut εvortex (min ((α/2)/4) (1/4:ℝ)) hnum hδsmall hεearlyVortex hξGeo hζcut.le hεcut.le hδcutBound hhrefcap
      hρ₀1 hθhalf hm le_rfl (hearlyCap.trans hAbsCap) (hearlyCap.trans hVCap) hEarly
  obtain ⟨rateParent,ζcert,δDeep,rate,hrate,hrateRoot,hrateInner,hrateEnd,hscale',hζ,hζrate,hζcap,hPreHostChunksRest1⟩:=hPreHostChunks
  obtain ⟨hζlimit',hδDeep,hδα,hrateDeep,p,εsup,capSmall,δsample,ν,hp,hp1,hpθ,hPreHostChunksRest2⟩:=hPreHostChunksRest1
  obtain ⟨hsqrt,hεsup,hεsupCap,hcapSmall,hcapOther,hcapEll,hδsample,hν,hνcap,Norder,hNorder,τcover,hPreHostChunksRest3⟩:=hPreHostChunksRest2
  obtain ⟨hτeq,hτ,hτcap,hτ1,hsafe1,hsafe2,hsafe3,hfinish,hbudgetE,hbudgetH,eps,γgeo,hPreHostChunksRest4⟩:=hPreHostChunksRest3
  obtain ⟨aLoad,ξroot,η₀,ηbal,ηInitial,heps,heps1,hγ,hgeometry,hcover,ha,ha1,hPreHostChunksRest5⟩:=hPreHostChunksRest4
  obtain ⟨hacapSmall,haκ,haγ,haedit,hξeq,hξ,hξγ,hξcap,hηeq,hη₀,hη,hη₀cap,hPreHostChunksRest6⟩:=hPreHostChunksRest5
  obtain ⟨hηγ,hηI,hηIcap,hsmall,hsmall',hellBound,δInitial,hδInitial,hδIα,hδIη,hcallbacks,δedit,hPreHostChunksRest7⟩:=hPreHostChunksRest6
  obtain ⟨ηedit,ηBudget,capChosen,hδedit,hδαedit,hδbal,hηedit,hBudget,hBudgetη,hsmallBudget,hChosen,hChosen1,hPreHostChunksRest8⟩:=hPreHostChunksRest7
  obtain ⟨hChosenBudget,d,hd,hmargins,bHub,Bweight,ξdeep,tOuter,ζouter,δOuter,δcap,rateOuter,hPreHostChunksRest9⟩:=hPreHostChunksRest8
  obtain ⟨ξedit,ξAbs,hb,hbc,hB,hBbound,hξdeep,hξdeepcap,hβchoose,htOuter,hζouter,hζlimitOuter,hPreHostChunksRest10⟩:=hPreHostChunksRest9
  obtain ⟨hδOuter,hδαOuter,hδcap,hδζ,hrateOuter,htrace,houterChoice,hjoint,hAfterLosses⟩:=hPreHostChunksRest10
  have hjointKeep:=hjoint
  obtain ⟨δ,θmatch',κplace,bplace,zplace,matchErr,σbal,κprime,dNeed,hStage,βSel,lamSel,ζSel,smin,K,rank,hSpacing,
    ζret,Nplace,lamMatch,aRow,γrow,BO,hPlacementAfter,hMatching,hBO,hd',hSelect,τmatch,tMatch,ξMatch,bMatch,hChoice,hColumns,
    hξedit,hξeditCap,hξeditBudget,hξeditσ,hξeditList,hξeditMatch,hColumnsAt,hξAbs,hξAbsCap,hξAbsBudget,hξAbsσ,hξAbsh,hCorrection⟩:=hjoint
  refine ⟨ξedit,hξedit,?_⟩
  intro χ hχ hχ1
  obtain ⟨capFailure,hcapFailure,Nfailure,hNfailure,hfailure⟩:=ordinary_triangle_failure_budget_before_absorber χ hχ
  let t:ℝ:=capFailure/2
  have ht:0<t:=by dsimp [t];positivity
  have htCap:t≤capFailure:=by dsimp [t];linarith only [hcapFailure]
  have hAfterLossesChunks :=
      hAfterLosses t t t t t t t t t ht ht ht ht ht ht ht ht ht
  obtain ⟨βsmall,r,hβsmall,hβold,hr,hrI,hrD,hrE,hrS,hrG,hrEnd,hrRows,hAfterLossesChunksRest1⟩:=hAfterLossesChunks
  obtain ⟨hselected',εTri,β,hεTri,hβ,hβone,hβα8,hβα4,hβκ,hβcap,hβδ,hβtri,hAfterLossesChunksRest2⟩:=hAfterLossesChunksRest1
  obtain ⟨hβcert,hβI,hβD,hβE,hβG,hgapOuter,hgapInner,hβbalance,v₀,Mhost,Mcut,hv₀,hAfterLossesChunksRest3⟩:=hAfterLossesChunksRest2
  obtain ⟨hMhost,hMcut,hafter,hselector,hcuts,vInner,hvInner,hInner,Msmall,vCert,vCommon,hMsmall,hAfterLossesChunksRest4⟩:=hAfterLossesChunksRest3
  obtain ⟨hvCert,hvouter,hvinner,hvcert,hcert,mInitial,mBalance,mEdit,Nedit,mFineInitial,mFineLater,mGeom,hAfterLossesChunksRest5⟩:=hAfterLossesChunksRest4
  obtain ⟨mAll,hmI,hmB,hmEdit,hmGeom,hI,hB',hE',hFI,hFL,hG,hInitAt,hAfterLossesChunksRest6⟩:=hAfterLossesChunksRest5
  obtain ⟨hBalance,hMargins,hFine,hLater,hGeom,M,vCommon',mVortex,mv,hM,hSmall,hN₀',hAfterLossesChunksRest7⟩:=hAfterLossesChunksRest6
  obtain ⟨hNcert,hNedit,htwo,hmatchBound,hvCert',hvOuter,hvInner',hmAll,hmv,hCommon,hVortexSize,hterm,hAfterLossesChunksRest8⟩:=hAfterLossesChunksRest7
  obtain ⟨hhostSize,hcutSize,hlook,hcert',hThresholds⟩:=hAfterLossesChunksRest8
  have hThreshold:=hThresholds t t t t t t t t t t t t ht ht ht ht ht ht ht ht ht ht ht ht
  obtain ⟨δ,θmatch',κplace,bplace,zplace,matchErr,σbal,κprime,dNeed,hStage,βSel,lamSel,ζSel,smin,K,rank,hSpacing,
    ζret,Nplace,lamMatch,aRow,γrow,BO,hPlacementAfter,hMatching,hBO,hd',hSelect,τmatch,tMatch,ξMatch,bMatch,hChoice,hColumns,
    hξedit',hξeditCap,hξeditBudget,hξeditσ,hξeditList,hξeditMatch,hColumnsAt,hξAbs,hξAbsCap,hξAbsBudget,hξAbsσ,hξAbsh,hCorrection,hTerminal,
    aAbs,bAbs,aEvent,haEvent,Nsel,Ncorr,Nc,Ng,Nh,Ncol,Ngeom,hNcorr,hNc,hNg,hNh,hNcol,hNgeom,hsel,hcorr,hgeom⟩:=hThreshold
  have hsminEq:smin=βfreq/200:=by obtain ⟨_,_,_,_,_,h,_⟩:=hSpacing;exact h
  subst smin
  have hK:0<K:=by obtain ⟨_,_,_,_,_,_,_,_,_,h,_⟩:=hSpacing;omega
  have hda:1/θmatch'≤(d:ℝ):=by obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,h,_⟩:=hSpacing;exact h
  have hterminal:=hTerminal rate ξroot hrateDeep.le hξ.le (2*mv) (2*mv) aAbs bAbs
  have hβvα:β≤α/8:=by nlinarith only [hβα8,hα]
  have hε1:ε≤1:=by linarith only [hεsmall]
  have hερ:ε≤ρ₀/16:=hεearly.trans hεearlyρ
  obtain ⟨Ntransfer,htransfer⟩:=ordinary_triangle_same_sample_event_to_preparation
    m kMatch d K mv (2*mv) aAbs bAbs Nsel Ncorr Nc Ng Nh Ncol Ngeom Nplace dNeed N₀ M hd'
    βfreq ρ₀ α θmatch' θ lamMatch aRow γrow ζSel lamSel ζSel τmatch tMatch ξMatch bMatch σbal t
    t t t t t t t aEvent ε εabs εv β ξAbs t t t t BO hsel hgeom hcorr
    ηBudget capChosen (5*ρ₀*(βfreq/200)^2/128) lamPlace ζPlace δ κplace bplace zplace matchErr κprime ζret ξedit rate ξroot
    hm hK hda hBudget hChosenBudget hStage hPlacementAfter hMatching hξedit.le hξeditσ hterminal χ capFailure Nfailure hfailure
    htCap htCap htCap htCap htCap htCap htCap htCap htCap htCap htCap htCap
    hρ₀ hα hθhalf hβfreq hε (by omega) (by omega) hβ.le hβone hN₀' htwo hterm
    v₀ κ aLoad ξdeep bHub Bweight ηhub δcap t t r r t t t hafter (by omega)
    kParent Mhost Mcut βP 1 ηH βH cParent Bparent εTri t (2*δref) href t hpstar hselector hcuts
    hε1 hερ hβvα hβtri hhostSize hcutSize cInner CInner ξInner cInner BInner ηhub Kdom eParent hParent capInner t t tpot vInner hInner (by omega)
    htCap htCap htCap htCap htCap htCap htCap htCap htCap
  let aBound:=2^((2*mv)*(2*mv))*aAbs
  let bBound:=2^((2*mv)*(2*mv))*bAbs
  let B:=max 1 (aBound*aBound+aBound*bBound)
  let N:=max 2 (max mv (max M Ntransfer))
  refine ⟨B,N,by dsimp [B];omega,by dsimp [N];omega,?_⟩
  intro n hn P D q hreg hEven hdegree ρ hρlo hρhi F hF hthreshold habundance
  have hn0:0<n:=by dsimp [N] at hn;omega
  have hρlo':ρ₀≤ initialIndexDensity (Fin q) D:=by simpa [ρ,initialIndexDensity] using hρlo
  have hρhi':initialIndexDensity (Fin q) D≤1:=by simpa [ρ,initialIndexDensity] using hρhi
  have hhalf:(Fintype.card (Fin n):ℝ)/2≤D:=by
    simp only [Fintype.card_fin]
    have hnreal:0≤(n:ℝ):=by positivity
    have hh:0≤(θ+α₀-1/2)*(n:ℝ):=mul_nonneg (by linarith only [hθhalf,hα₀]) hnreal
    nlinarith only [hdegree,hh]
  have hD:0<D:=by
    have hnreal:0<(n:ℝ):=by exact_mod_cast hn0
    have hpositive:0<θ+α₀:=by linarith only [hθhalf,hα₀]
    have hprod:0<(θ+α₀)*(n:ℝ):=mul_pos hpositive hnreal
    have :0<(D:ℝ):=lt_of_lt_of_le hprod hdegree
    exact_mod_cast this
  obtain ⟨Qlook,π,hπ,hnoshort⟩:=hlook (Fin n) (Fin q) P D mv hreg hhalf hρlo' hρhi' hVortexSize (by dsimp [N] at hn;simp;omega)
  let Q:=Qlook.toVortex
  have hdegree':(θ+α)*(n:ℝ)≤D:=by
    have hnreal:0≤(n:ℝ):=by positivity
    nlinarith only [hdegree,mul_nonneg (sub_nonneg.mpr hαsub) hnreal]
  have hAllowed:∀u,AllowedCycleLengths (F u) Set.univ:=by intro u v;trivial
  obtain ⟨i₀,rsv,Cres,sampling,w,seed,hwitness,hpoint,hinputs,selection,hprepared⟩:=
    htransfer n q D (by dsimp [N] at hn;omega)
      (by simpa only [Fintype.card_fin] using (first_vortex_hub_cardinality_le_host (U:=Fin q) hreg hn0 hD hρhi')) F hF habundance hthreshold Set.univ hAllowed P hreg hdegree' hρlo' hρhi' Q π hπ hnoshort
  obtain ⟨endpointWeight,hresult⟩:=hprepared (R:=fun _=>Unit) (fun _=>FiniteLaw.uniform Unit)
  have hsplit:=hresult
  have hβnorm:(βH/2)/2=βH/4:=by ring
  have hδnorm:(2*δref)/2=δref:=by ring
  have hεnorm:((2*ηH+gapRoot)+(εstar-(2*ηH+gapRoot)))=εstar:=by ring
  have hprob:=hsplit (by
    intro z hEvent hTests hComp hCycle hLevels hCosts
    exact ordinary_triangle_assigned_wheel_callback_on_common_outcome
      (mAbs:=2*mv) (tAbs:=2*mv) (aAbs:=aAbs) (bAbs:=bAbs)
      d kParent (by omega) ρ₀ (ρ₀*(βfreq/200)/2) hrefLocal δcut ζcut εcut ζlimit εsample
      ε ξroot aLoad κ β ηbal 1 (α/2) ζcert cBoundary δDeep rate rateParent
      mBalance mFineLater mInitial ηInitial δInitial hInitAt hBalance hLater hζlimit' hζrate hζcut.le hεcut.le hζlimit.le
      P D mv Q π hπ (ordinaryAssignedSpokeProbability F hF K i₀ rsv θmatch' ((m:ℝ)+1)) F Cres
      (Finset.univ\Q.extendedVertices 1) (Q.extendedVertices Q.length) (Q.extendedIndices Q.length) ξAbs
      (ordinaryTriangleAssignedReservoirCost d δ aRow γrow ξedit σbal sampling.u)
      (2*(initialIndexDensity (Fin q) D*rsv/2)) rsv θ r r cInner (4*CInner/(ρ₀*(βfreq/200)/2)^7) ηhub capInner (eParent*ε) (hParent*ε)
      βP 1 ηH βH cParent Bparent εTri (βH/2) (2*δref) href (2*ηH) gapRoot ζroot lamFine N₀
      (βH/8) (cLinear*τcover) ξGeo ζGeo p eps lam γgeo edit βe βh (εstar-(2*ηH+gapRoot)) mGeom
      (href/4) cLinear τcover ellCap capSmall lamInner
      hreg (by simpa using hn0) hhalf hρ₀ hρlo' hρhi'
      (hB'.trans (hmAll.trans hCommon)) (hFL.trans (hmAll.trans hCommon)) (hI.trans (hmAll.trans hCommon)) (hG.trans (hmAll.trans hCommon))
      hβ.le hβone hε (by omega) hrateDeep.le hξ.le hζcap hθhalf
      (by
        simp only [Fintype.card_fin]
        have hnreal:0≤(n:ℝ):=by positivity
        have hh:0≤(α₀-α/2)*(n:ℝ):=mul_nonneg (by linarith only [hα,hαsub]) hnreal
        nlinarith only [hdegree,hh])
      hr.le hrD hrS hr.le hrD hrS
      (by positivity) (mul_le_mul_of_nonneg_right heB hε.le) (by positivity) (mul_le_mul_of_nonneg_right hhB hε.le)
      hrI hrI hηIcap hδcutBound hhrefcap hBparent.le hζroot.le hN₀ hscale' hfine hξ.le ha.le hη.le hcParent.le
      hlamPos.le hlam1 hlamFineBound
      (by
        obtain ⟨_,_,_,_,hrsv0,hrsv1,_,_⟩:=ordinary_assigned_wheel_sample_inputs F hF P hreg hD K i₀ rsv θmatch' ((m:ℝ)+1) ρ₀ (βfreq/200) d hρ₀ hρlo' hρhi' (by positivity) sampling
        rw [hβnorm]
        exact hGeom rsv hrsv0.le hrsv1)
      hrate.le hrateInner hEllPos.le hcapSmall.le hellBound hξcap hpack hβePos.le rfl selection.weight
      εrows tpot ν M vCommon' (by rw [hδnorm,hεnorm];exact hcert') hCommon hterm hrRows hrRows hbudgetE hbudgetH hfinish endpointWeight
      hF K i₀ rsv θmatch' ((m:ℝ)+1) (βfreq/200) (by positivity) sampling rfl rfl rfl rfl
      mEdit Nedit mFineInitial 1 cInitial δedit ηedit ηBudget (by dsimp [N] at hn;omega) (hE'.trans (hmAll.trans hCommon))
      (by nlinarith only [hβα8,hα]) hBudgetη hζ.le hsmallBudget hMargins hrE hrE
      (mul_le_mul_of_nonneg_right heI hε.le) (mul_le_mul_of_nonneg_right hhI hε.le) hFine (hFI.trans (hmAll.trans hCommon))
      (by rw [hβnorm];exact hgeometry)
      δInner 1 1 eParent eParent hγ hlamρ hξGeo.le hεξV hερV (by rw [hlamEq])
      (by positivity) hedit hβG hrG hrG hξγ haγ hηγ
      (by simpa using hrow) (by norm_num at hlevel ⊢;exact hlevel)
      haedit hlamE hlamH
      hNcert htwo (by obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,hinner,_⟩:=hselected;exact hinner.delta_pos.le)
      hrEnd hrEnd hrateEnd (by norm_num) (by norm_num) he (le_refl _) _ z hEvent hTests hComp hCycle hLevels
      (by
        have hdec : (instDecidableEqFin n : DecidableEq (Fin n)) = Classical.decEq (Fin n) :=
          Subsingleton.elim _ _
        have hdecq : (instDecidableEqFin q : DecidableEq (Fin q)) = Classical.decEq (Fin q) :=
          Subsingleton.elim _ _
        convert hCosts using 1 <;> congr! 10
        all_goals
          dsimp only
          repeat rw [hdec]
          repeat rw [hdecq]
          rename_i Kres JQ JH
          let cost : ℝ := ordinaryTriangleAssignedReservoirCost d δ aRow γrow ξedit σbal sampling.u Kres
          exact Iff.of_eq (congrArg (fun inst : DecidableEq (Fin q) =>
            (@OrdinaryCorrectedProtectedReservoirWitness (Fin n) (Fin q) _ _
              (Classical.decEq (Fin n)) inst 3 (2*mv) (2*mv) aAbs bAbs ξAbs
              ((rawWheelGraph P (fun e => expandedOrdinarySelectedCollapse e (z.1.fst e))) \
                permutationConflictGraph π (3*d))
              (permutationConflictGraph π (3*d))
              (@rawWheelSpokes (Fin n) (Fin q) Bool Bool (Classical.decEq (Fin n)) π d
                (fun e => expandedOrdinarySelectedCollapse e (z.1.fst e)) false)
              (@SDiff.sdiff (Finset (Fin n)) (@Finset.instSDiff (Fin n) (Classical.decEq (Fin n)))
                Finset.univ (Q.extendedVertices 1)) (Q.extendedVertices 1)
              (Q.extendedVertices Q.length) (Q.extendedIndices Q.length)
              (Q.extendedIndices 1) Kres JQ JH →
              0 ≤ cost ∧ cost ≤ 14*ηBudget*n ∧
              cost + 2*((3*d:ℕ):ℝ) ≤ 15*ηBudget*n)) (Subsingleton.elim _ _))))
  refine ⟨Q.extendedVertices 1,?_,?_⟩
  · have hh:((Q.extendedVertices 1).card:ℝ)≤ε*n:=by
      simpa only [Fintype.card_fin] using marked_initial_inner_vertex_bound Q hε.le
    have hnreal:0≤(n:ℝ):=by positivity
    exact hh.trans (mul_le_mul_of_nonneg_right hεmax hnreal)
  · have hprob' := hprob
    simp only [initialIndexDensity,Fintype.card_fin] at hprob'
    dsimp [ρ]
    apply hprob'.trans
    apply finiteLaw_probability_mono
    intro σ hPrep
    obtain ⟨A,hA,hcard,hdecomp⟩:=hPrep
    exact ⟨A,hA,hcard.trans (le_max_right _ _),hdecomp⟩
end Oberwolfach
