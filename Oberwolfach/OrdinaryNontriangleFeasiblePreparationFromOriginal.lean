module

public import Oberwolfach.OrdinaryDeepOriginalStaticRowsWithOriginalCapAndSize
public import Oberwolfach.OrdinaryNontriangleFeasibleReduction
public import Oberwolfach.OrdinaryJointFinePreparationWithExtraSize
public import Oberwolfach.OrdinarySelectedCostRateMono
public import Oberwolfach.OrdinaryDeepCommonSampleFailureBudget
public import Oberwolfach.OrdinaryParentAssignedReadyPointwiseOutcome
public import Oberwolfach.OrdinaryGeneralCommonProbabilityWithDerivedInputs
public import Oberwolfach.FirstVortexHubCardinality

@[expose] public section
/-! The nontriangle feasible branch of protected preparation under the
original assumptions, with matching, correction and wheel certificates on the
same sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 150000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_nontriangle_feasible_preparation_from_original : OrdinaryNontriangleFeasibleProtectedPreparation :=by
  intro θhost α₀ εmax ρ₀ βfreq hθhost hθhost1 hα₀ hεmax hρ₀ hρ₀1 hβfreq hβfreq1 rstar hr hcycle
  obtain ⟨α,hα,hαsub,c,C,hc,hC,Kdeep,hKdeep,aDeep,ε₀,ρdeep,θdeep,haDeep,hε₀,hρdeep,hθdeep,hdeepEarly,
    δAbs,hAbs,εabs,εv,hCorr,hInner,hInnerA,hInnerρ,hInner8,hInnerAbs,hInnerV,
    m,k,βPlace,lamPlace,ζPlace,εearly,dMin,hAt,hEarly,hTail,ηP,hηP,hηPcap,hparent⟩:=
    ordinary_deep_original_static_rows_with_original_cap_and_size 1 rstar βfreq ρ₀ α₀ θhost 1 1 1 1 εmax 1 1 1
      hr hβfreq hβfreq1 hρ₀ hρ₀1 hα₀ hθhost hθhost1 hcycle (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hεmax (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨δref,href,βP,rowParent,kParent,βH,cParent,Bparent,εstar,cLinear,hδref,hδsmall,hhref,hβP,hrowParent,hkParent,hβH,hcParent,hBparent,hεstar,hcLinear,hRule,
    εCert,cCert,hεCert,hcCert,hRef,
    ηH,gap,ζcap,geomGap,hηH,hηHcap,hgap,hgapcap,hζcap,hζh,hζlimit,hGeomGap,hgeomGap,hgeomEq,
    hrefCut,δlimit,geomCap,hhrefCut,hhrefcap,hδlimit,hδlimitcap,hgeomCap,hgeomCapBound,hGeometry,
    ζparent,rateParent,lamroot,hζparent,hrateParent,hlamroot,hζparentcap,
    N₀,hN₀,hScale,hRoot,hScaleMono,hEvent,hHost⟩:=hparent
  have hPreparedBulkChunks1 :=hEvent
  obtain ⟨δcut,ζcut,εcut,ζlimit,εsample,εvortex,cBoundary,cInitial,βout,ξreserve,ζout,edit,hPreparedBulkChunks1Rest1⟩:=hPreparedBulkChunks1
  obtain ⟨hδcut,hδquarter,hδcutlimit,hζcut,hεcut,hζlimit',hεsample,hεvortex,hεvquarter,hBoundary,hInitial,hNumeric,hPreparedBulkChunks1Rest2⟩:=hPreparedBulkChunks1Rest1
  obtain ⟨hβout,hβeq,hξreserve,hζout,hedit,hξcap,hζcap',γcert,eParent,hParent,κ,hγcert,hPreparedBulkChunks1Rest3⟩:=hPreparedBulkChunks1Rest2
  obtain ⟨heParent,hhParent,hγe,heBoundary,hhBoundary,heInitial,hhInitial,hκ,hκ1,hκρ,hpstar,hpstar1,hPreparedBulkChunks1Rest4⟩:=hPreparedBulkChunks1Rest3
  obtain ⟨ηhub,ζhub,aEnd,ηend,ζlocal,δend,hηhub,hζhub,haEnd,haEnd1,hηend,hζlocal,hPreparedBulkChunks1Rest5⟩:=hPreparedBulkChunks1Rest4
  obtain ⟨hδend,εcap,hεcap,hεmaxCap,hεearlyCap,hεinnerCap,hεhubCap,hεaCap,hερCap,cMatch,eCleanup,hCleanup,hPreparedBulkChunks1Rest6⟩:=hPreparedBulkChunks1Rest5
  obtain ⟨lam,ε,βe,βh,θmatch,hcMatch,heCleanup,hhCleanup,hcMatchcap,hβeeq,hβheq,hβe,hPreparedBulkChunks1Rest7⟩:=hPreparedBulkChunks1Rest6
  obtain ⟨hβh,hlam,hlamroot,hlamquarter,hlamρ,hlamβe,hlamβh,hrow,hlevel,hε,hεcap',hεvortex',hPreparedBulkChunks1Rest8⟩:=hPreparedBulkChunks1Rest7
  obtain ⟨hεquarter,hεξ,hεξρ,hεroot,hθeq,hθ,hEventDeep⟩:=hPreparedBulkChunks1Rest8
  obtain ⟨ξdeep,bDeep,Kdom,Bweight,hξdeep,hξdeepcap,hbDeep,hbDeepc,hbDeepcap,hKdom,hBweight,hKdom1,hKdom2,hWeight,hβchoose,
    tHub,eEvent,hEvent,capHub,costRate,htHub,heEvent,hhEvent,hcapHub,hebound,hhbound,hcostRate,hcostAt,
    rateLocal,ζ,δDeep,rate,hrateLocal,hrateEnd,hrateLocalParent,hζ,hζlim,hζrate,hζcapHub,hδDeep,hδDeepα,hrate,hratecost,hselected,hDeepSelect⟩:=hEventDeep
  have hPreparedBulkChunks2 :=hselected
  obtain ⟨ellCap,kcap,pbound,p,εsup,finishCap,δsample,loadCap,ν,cap,hellEq,hell,hPreparedBulkChunks2Rest1⟩:=hPreparedBulkChunks2
  obtain ⟨hkcap,hpbound,hpcap',hp,hpp,hp1,hpθ,hsqrt,hεsup,hεsupcap,hfinish,hfinishA,hPreparedBulkChunks2Rest2⟩:=hPreparedBulkChunks2Rest1
  obtain ⟨hfinishell,hδsample,hload,hload1,hloadfinish,hν,hcap,hνfinish,hcapfinish,Nfinish,hschedule,τcover,hPreparedBulkChunks2Rest3⟩:=hPreparedBulkChunks2Rest2
  obtain ⟨ηpack,hτeq,hτ,hτcap,hτ1,hηpack,hlinear,n₀,εout,γgeom,aLoad,ξroot,hPreparedBulkChunks2Rest4⟩:=hPreparedBulkChunks2Rest3
  obtain ⟨η₀,ηbal,ηInitial,βcap,δcap,δInitial,δedit,ηedit,hεout,hεout1,hγgeom,haLoad,hPreparedBulkChunks2Rest5⟩:=hPreparedBulkChunks2Rest4
  obtain ⟨haLoad1,haLoadCap,haLoadA,haLoadγ,haLoadEdit,hξeq,hξroot,hξε,hξγ,hξsq,hellRate,hcoverRate,hPreparedBulkChunks2Rest6⟩:=hPreparedBulkChunks2Rest5
  obtain ⟨hηeq,hη₀,hηbal,hηbal₀,hηbalγ,hηInitial,hηInitialBal,hβcap,hβcap1,hβcapγ,hδcap,hδcapγ,hPreparedBulkChunks2Rest7⟩:=hPreparedBulkChunks2Rest6
  obtain ⟨hδInitial,hδInitialα,hδInitialη,hδedit,hδeditα,hδeditη,hηedit,hstatic,ηBudget,capChosen,hBudget,hBudgetη,hPreparedBulkChunks2Rest8⟩:=hPreparedBulkChunks2Rest7
  obtain ⟨hsmall,hChosen,hOriginal,hCap,d,hd,ξedit,ξAbs,hξcapEdit,hξcapAbs,hjoint,hthresholds,hPreparedBulkChunks2Rest9⟩:=hPreparedBulkChunks2Rest8
  obtain ⟨rowTolerance,hrowTolerance,hrowInitial,hrowDeep,hrowEdit,hrowSample,hrowGeom,hrowEnd,hrowCap,hremain⟩:=hPreparedBulkChunks2Rest9
  have hjointKeep:=hjoint
  obtain ⟨δ,θ,κplace,bplace,zplace,matchErr,σbal,κprime,dNeed,hStage,βSel,lamSel,ζSel,smin,K,rank,hSpacing,
    ζret,Nplace,lamMatch,aRow,γrow,BO,hPlacementAfter,hMatching,hBO,hd',hSelect,τmatch,tMatch,ξMatch,bMatch,hChoice,hColumns,
    hξedit,hξeditCap,hξeditBudget,hξeditσ,hξeditList,hξeditMatch,hColumnsAt,hξAbs,hξAbsCap,hξAbsBudget,hξAbsσ,hξAbsh,hCorrection⟩:=hjoint
  refine ⟨ξedit,hξedit,?_⟩
  intro χ hχ hχ1
  obtain ⟨t,ht,Nfailure,hNfailure,hfailure⟩:=ordinary_deep_common_sample_failure_budget χ hχ
  obtain ⟨Nclean,Nreserve,Ncert,hcert,M,hM,hN₀M,hbase,hfour,hbudget,hcostExtra,hsource⟩:=hremain d
  let capInner:ℝ:=min (min aDeep (min (ρ₀/16) (1/8:ℝ))) (min εabs εv)
  let αcut:ℝ:=min (α/8) (1/4:ℝ)
  have hε1:ε<1:=by linarith only [hεquarter]
  have hερ:ε≤ρ₀/16:=hεcap'.trans hερCap
  have hεearly:ε≤εearly:=hεcap'.trans hεearlyCap
  have habs:ε≤εabs:=hεcap'.trans (hεinnerCap.trans hInnerAbs)
  have hv:ε≤εv:=hεcap'.trans (hεinnerCap.trans hInnerV)
  have hδlim:δcut≤min (αcut/32) ((ρ₀*(βfreq/200)/2)/512):=hδcutlimit.trans hδlimitcap
  have hbalcap:ηbal≤δcut*(ρ₀/8)*ξroot/1000:=by simpa only [hηeq] using hηbal₀
  have hdeep:=hDeepSelect aLoad rowTolerance rowTolerance haLoad haLoadA hrowTolerance hrowTolerance t t t t t ht ht ht ht ht
  have hParentSelected:=hHost d hd ε t t hε hε1 ht ht
  have hcost:=ordinary_selected_cost_rate_mono ε ρ₀ capHub d rate costRate hratecost (hcostAt d)
  obtain ⟨εTri,β,hεTri,hβ,hβone,hβα,hβεTri,hβcap',hβInitial,hβDeep,hβEdit,
    mv,mCert,Nmin,Nfine,hpayload,hmCert,hNmin,hMN,hNsize,hNterminal,hBundle⟩:=
    ordinary_joint_fine_preparation_with_extra_size 1 rstar d m k dMin Kdeep kParent hd (by omega)
      βfreq ρ₀ α (α/2) capInner capChosen θhost (by omega) hβfreq hβfreq1 hρ₀ hρ₀1 hα hθhost
      βPlace lamPlace ζPlace εearly ε capHub ηBudget δAbs hAbs εabs εv ξedit ξAbs hjointKeep
      hε hεquarter hερ habs hv 10 t t t t t t t t t t t t
      ht ht ht ht ht ht ht ht ht ht ht ht
      αcut c C aDeep ε₀ ρdeep θdeep aLoad ξdeep bDeep Bweight ηhub Kdom t t eParent hParent rowTolerance rowTolerance t t t capHub 1
      hrowTolerance hrowTolerance hβchoose hdeep βP ηP rowParent ηH βH cParent Bparent t δref href t hpstar hParentSelected
      βcap δInitial δDeep δedit t hβcap hδInitial hδDeep hδedit ht
      lam ξreserve ξroot ηbal ηInitial γgeom edit p βe βh (βH/4)
      (cParent*(1-δref)^((rstar-1+1)-1)) (Bparent/((ρ₀/16)*(ρ₀*(βfreq/200)/2)^(2*(rstar-1+1)-1)))
      (2*ηH+gap) geomGap βout ζout ηpack εout rate hξroot.le
      (ρ₀*(βfreq/200)/2) hrefCut δcut ζcut εcut ζlimit εsample cBoundary cInitial 1 ζ rate δcap ηedit
      hrowCap hrowCap M hsource hcost εvortex hNumeric hεvortex' hδcut hδquarter hξroot hξε haLoad haLoad1 hξsq
      hηbal.le hbalcap hζcut.le hεcut.le hζlimit'.le hδlim hhrefcap hAt hEarly hεearly hrate.le
  obtain ⟨δ₂,θ₂,κplace₂,bplace₂,zplace₂,matchErr₂,σbal₂,κprime₂,dNeed₂,hStage₂,βSel₂,lamSel₂,ζSel₂,smin₂,K₂,rank₂,hSpacing₂,
    ζret₂,Nplace₂,lamMatch₂,aRow₂,γrow₂,BO₂,hPlacementAfter₂,hMatching₂,hBO₂,hd₂,hSelect₂,τmatch₂,tMatch₂,ξMatch₂,bMatch₂,hChoice₂,hColumns₂,
    hξedit₂,hξeditCap₂,hξeditBudget₂,hξeditσ₂,hξeditList₂,hξeditMatch₂,hColumnsAt₂,hξAbs₂,hξAbsCap₂,hξAbsBudget₂,hξAbsσ₂,hξAbsh₂,hCorrection₂,hTerminal₂,
    aAbs,bAbs,aEvent,haEvent,Nsel,Ncorr,Nc,Ng,Nh,Ncol,Ngeom,hNcorr,hNc,hNg,hNh,hNcol,hNgeom,hsel,hcorr,hgeom,
    Nhost,hNhost,hselN,hcorrN,hgeomN,hmvN,hAll⟩:=hBundle (2*mv)
  have hsminEq:smin₂=βfreq/200:=by obtain ⟨_,_,_,_,_,h,_⟩:=hSpacing₂;exact h
  subst smin₂
  have hK:0<K₂:=by obtain ⟨_,_,_,_,_,_,_,_,_,h,_⟩:=hSpacing₂;omega
  have hda:1/θ₂≤(d:ℝ):=by obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,h,_⟩:=hSpacing₂;exact h
  have hTerminalSelected:=hTerminal₂ rate ξroot hrate.le hξroot.le (2*mv) (2*mv) aAbs bAbs
  have hMsize:2/ε≤(M:ℝ):=
    (div_le_div_of_nonneg_right (by norm_num : (2:ℝ)≤4) hε.le).trans hfour
  have hMterminal:(M:ℝ)≤ε*mv/2:=by
    have hMNreal:(M:ℝ)≤Nfine:=by exact_mod_cast hMN
    exact hMNreal.trans hNterminal
  obtain ⟨Ntransfer,htransfer⟩:=ordinary_general_common_probability_with_derived_inputs
    rstar m k d K₂ hd₂ (by omega) βfreq ρ₀ α θhost ε β δ₂ θ₂ aRow₂ γrow₂ σbal₂ lamMatch₂ lamPlace ξedit bMatch₂ rate ξroot
    (2*mv) (2*mv) aAbs bAbs N₀ M hN₀M hε hMsize hβ.le hβone
    Nplace₂ dNeed₂ ηBudget capChosen (5*ρ₀*(βfreq/200)^2/128) ζPlace κplace₂ bplace₂ zplace₂ matchErr₂ κprime₂ ζret₂
    (hAt.2.1) hK hda hBudget hCap hStage₂ hPlacementAfter₂ hMatching₂ hξedit.le hξeditσ₂ hρ₀ hα hθhost hβfreq hTerminalSelected
  let aBound:=2^((2*mv)*(2*mv))*aAbs
  let bBound:=2^((2*mv)*(2*mv))*bAbs
  let B:=max 1 (aBound*aBound+aBound*bBound)
  let N:=max 2 (max Nhost (max Ntransfer (max Nfailure Nfine)))
  refine ⟨B,N,by dsimp [B];omega,by dsimp [N];omega,?_⟩
  intro n hn P D qCount hreg hEven hdegree ρ hρlo hρhi F hF hthreshold habundance
  have hn0:0<n:=by dsimp [N] at hn;omega
  have hρlo':ρ₀≤ initialIndexDensity (Fin qCount) D:=by simpa [ρ,initialIndexDensity] using hρlo
  have hρhi':initialIndexDensity (Fin qCount) D≤1:=by simpa [ρ,initialIndexDensity] using hρhi
  have hhalf:(Fintype.card (Fin n):ℝ)/2≤D:=by
    simp only [Fintype.card_fin]
    have hnreal:0≤(n:ℝ):=by positivity
    have hh:0≤(θhost+α₀-1/2)*(n:ℝ):=mul_nonneg (by linarith only [hθhost,hα₀]) hnreal
    nlinarith only [hdegree,hh]
  have hD:0<D:=by
    have hnreal:0<(n:ℝ):=by exact_mod_cast hn0
    have hpositive:0<θhost+α₀:=by linarith only [hθhost,hα₀]
    have hprod:0<(θhost+α₀)*(n:ℝ):=mul_pos hpositive hnreal
    have :0<(D:ℝ):=lt_of_lt_of_le hprod hdegree
    exact_mod_cast this
  have hq:qCount≤n:=by
    simpa only [Fintype.card_fin] using (first_vortex_hub_cardinality_le_host (U:=Fin qCount) hreg hn0 hD hρhi')
  have hdegree':(θhost+α)*(n:ℝ)≤D:=by
    have hnreal:0≤(n:ℝ):=by positivity
    nlinarith only [hdegree,mul_nonneg (sub_nonneg.mpr hαsub) hnreal]
  obtain ⟨Qlook,π,hπ,hnoshort,hAll⟩:=hAll n qCount D (by dsimp [N] at hn;omega) hq F hF habundance hρlo' hρhi' hthreshold P hreg hdegree'
  let Q:=Qlook.toVortex
  obtain ⟨i₀,rsv,Cres,sampling,w,seed,hwitness,hpoint,hinputs,selection,hProb⟩:=
    hAll (fun _=>θhost+α/2-β/2) (fun i=>rowTolerance*(markedVortexInnerVertices Q i).card)
      (fun i=>rowTolerance*(markedVortexInnerHubs Q i).card)
  have hmv:0<mv:=by
    by_contra h
    have hzero:mv=0:=by omega
    have hNpositive:0<Nfine:=by
      have hh:(0:ℝ)<2/ε:=by positivity
      have hh':(0:ℝ)<Nfine:=lt_of_lt_of_le hh hNsize
      exact_mod_cast hh'
    rw [hzero] at hNterminal
    norm_num at hNterminal
    omega
  have hAllowed:∀u,AllowedCycleLengths (F u) Set.univ:=by intro u v;trivial
  obtain ⟨innerWeight,hWeightSetup,hProb⟩:=hProb (R:=fun _=>Unit) (fun _=>FiniteLaw.uniform Unit)
  let loss0:ℝ:=(((((((0+3*t+t)+2*t)+t)+t)+t)+t)+t)
  let loss:ℝ:=loss0+t+t+t+2/(n:ℝ)^10+(1/(n:ℝ)+2/(n:ℝ)^2)+t
  let bprob:ℝ:=1-(loss+t+t+t+t+t)-t-t-t
  let pRaw:=initialIndexDensity (Fin qCount) D*rsv/2
  let p₂:=ordinaryAssignedApproxRimProbability F hF i₀ rsv θ₂ ((m:ℝ)+1) D
  let marks:=ordinaryAssignedMarkedProbability F hF K₂ θ₂ ((m:ℝ)+1)
  let spokes:=ordinaryAssignedSpokeProbability F hF K₂ i₀ rsv θ₂ ((m:ℝ)+1)
  let Rextra:(∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e)→Type:=fun _=>Unit
  let νextra:∀σ,FiniteLaw (Rextra σ):=fun _=>FiniteLaw.uniform Unit
  let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) pRaw 0 p₂ 0 sampling.u
    sampling.hp (by norm_num) sampling.hp₂ (by norm_num) sampling.hu sampling.hsum d hd₂ marks sampling.hq sampling.hQ spokes sampling.hs sampling.hS)
  let E:=OrdinaryAssignedCorrectionEvent rstar d (2*mv) aAbs bAbs (2*mv) 10 n qCount K₂ D hd₂
    (θ₂/2) t t t t ξAbs P (permutationConflictGraph π (3*d)) π F hF i₀ rsv θ₂ ρ₀ (βfreq/200) m sampling
    (Finset.univ\Q.extendedVertices 1) (Q.extendedVertices 1) (Q.extendedVertices Q.length)
    (Q.extendedIndices Q.length) (Q.extendedIndices 1) (Q.extendedIndices 1)
    Rextra νextra t t t t t t t t Cres lamMatch₂ aRow₂ γrow₂ σbal₂ aEvent ζSel₂ lamSel₂ bMatch₂ w seed tMatch₂ ξMatch₂
  let Good:=OrdinaryDeepRowsCutsEvent n qCount D mv (rstar-1) Kdeep d β ε P Q π hπ
    pRaw rsv (ρ₀*(βfreq/200)/2) αcut c C bDeep Bweight ξdeep ηhub Kdom aDeep aLoad ρdeep θdeep capHub eParent hParent rowTolerance rowTolerance
    (fun _=>θhost+α/2-β/2) (fun i=>rowTolerance*(markedVortexInnerVertices Q i).card)
    (fun i=>rowTolerance*(markedVortexInnerHubs Q i).card) spokes false Rextra μ νextra E loss t t t t t
  let All:=OrdinaryVortexParentProductEvent n qCount D mv (rstar-1) kParent d (Q.length-1) (by omega) hd₂ β ε (α/2) ρ₀
    (ρ₀*(βfreq/200)/2) βP ηP rowParent ηH βH cParent Bparent εTri t δref href hpstar P Q π hπ selection pRaw rsv spokes false Rextra Good
  let Extra:(Σσ:∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e,Rextra σ)×(Sym2 (Fin n)→Bool)→Prop:=fun z=>OrdinaryVortexThreeStepRowIndexEvent 3 d rowTolerance rowTolerance P (permutationConflictGraph π (3*d)) D mv β ε Q π hπ (2*pRaw) rsv spokes false
      (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e)) ∧
    OrdinaryVortexThreeStepEditedBalanceEvent P D mv β ε rsv rowTolerance rowTolerance Qlook π hπ d false
      (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))
  let Common:=fun z=>All z ∧ Extra z
  have hCommon:bprob≤((μ.sigma νextra).prod (FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.fairCoin))).probability Common:=by
    exact hProb
  have hPrep:=htransfer n qCount D (by dsimp [N] at hn;omega) hq F hF habundance hthreshold Set.univ hAllowed P hreg hdegree' hρlo' hρhi'
    mv Q π hnoshort hmv hMterminal i₀ rsv Cres sampling w seed τmatch₂ tMatch₂ ξMatch₂ ζSel₂ lamSel₂ ζSel₂
    t t t t t t t t aEvent BO₂ hwitness 10 t t t t ξAbs (fun _=>Unit) (fun _=>FiniteLaw.uniform Unit)
    (FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.fairCoin)) Common bprob hCommon (by omega)
  have hscaleLocal:=hScaleMono rateLocal hrateLocalParent
  have hζparentHref:ζparent≤href:=hζparentcap.trans hζh
  have hNcertFine:Ncert≤Nfine:=by
    have hNcertM:Ncert≤M:=by dsimp only at hbase;omega
    omega
  have hN₀Fine:N₀≤Nfine:=by omega
  have hNminN:Nmin≤n:=by dsimp [N] at hn;omega
  have hβgeom:β≤γgeom/1000:=hβcap'.trans hβcapγ
  have hβhost:β≤2*(α/2):=by nlinarith only [hβα,hα]
  have hdegreeWheel:(θhost+α/2)*Fintype.card (Fin n)≤D:=by
    simp only [Fintype.card_fin]
    have hnreal:0≤(n:ℝ):=by positivity
    nlinarith only [hdegree,mul_nonneg (by linarith only [hα,hαsub] : 0≤α₀-α/2) hnreal]
  have hTransferred:=hPrep (by
    intro z hz hComp hCycle hLevels
    have hβnorm:(βH/2)/2=βH/4:=by ring
    have hpointwise:=ordinary_parent_assigned_ready_pointwise_outcome
      (mAbs:=2*mv) (tAbs:=2*mv) (aAbs:=aAbs) (bAbs:=bAbs)
      (rstar-1) Kdeep d kParent (by omega) hd₂ (by omega)
      ρ₀ (ρ₀*(βfreq/200)/2) hrefCut δcut ζcut εcut ζlimit εsample
      ε ξroot aLoad aDeep ρdeep θdeep β ηbal 1 (α/2) ζ cBoundary δDeep rate rateLocal ηInitial δInitial
      hrate.le hζlim hζrate hζcut.le hεcut.le hζlimit'.le
      P D mv Q π hπ spokes Rextra μ νextra E Extra F Cres
      (Finset.univ\Q.extendedVertices 1) (Q.extendedVertices Q.length) (Q.extendedIndices Q.length) ξAbs
      (ordinaryTriangleAssignedReservoirCost d δ₂ aRow₂ γrow₂ ξedit σbal₂ sampling.u)
      pRaw rsv θhost rowTolerance rowTolerance αcut c C ηhub capHub eParent hParent
      βP ηP rowParent ηH βH cParent Bparent εTri (βH/2) δref href (2*ηH) gap ζparent lamroot N₀
      βout ηpack ξreserve ζout p εout lam γgeom edit βe βh geomGap
      δend ζhub ζlocal γcert κ ν cap εsup δsample τcover n₀ Nclean Nreserve Ncert Nfinish M Nfine θmatch ellCap finishCap kcap geomCap cMatch
      hreg (by simpa using hn0) hhalf hρ₀ hρlo' hρhi' hβ.le hβone hε hmv hζcapHub hθhost hdegreeWheel
      hrowTolerance.le hrowDeep hrowSample hrowTolerance.le hrowDeep hrowSample
      (by positivity) (mul_le_mul_of_nonneg_right heBoundary hε.le)
      (by positivity) (mul_le_mul_of_nonneg_right hhBoundary hε.le)
      hrowInitial hrowInitial hηInitialBal hδlim hhrefcap hBparent.le hpstar hζparent.le hN₀
      hscaleLocal hRoot hξroot.le haLoad.le hηbal.le hcParent.le hlam.le hlamquarter hlamroot
      hNcertFine hNsize hNterminal hN₀Fine hMN hδend.le hrowEnd hrowEnd hrateEnd hrateLocal.le
      hζhub hζlocal hγcert hγe hκρ hθ hθeq hcMatchcap hζparentHref hgeomCapBound hξcap hζcap'
      hεsupcap hpθ hsqrt hellRate hcoverRate hschedule
      bDeep Bweight ξdeep Kdom loss t t t t t t selection hinputs
      hF (by simpa only [Nat.sub_add_cancel (by omega : 1≤rstar)] using hComp)
      K₂ i₀ rsv θ₂ ((m:ℝ)+1) (βfreq/200) (by positivity) sampling rfl rfl rfl rfl
      ηedit ηBudget cInitial δedit hrowEdit hrowEdit
      (mul_le_mul_of_nonneg_right heInitial hε.le) (mul_le_mul_of_nonneg_right hhInitial hε.le)
      hβhost hBudgetη hζ.le hsmall
      (by rw [hβnorm];simpa only [Nat.add_sub_cancel] using hstatic)
      hγgeom hlamρ hξreserve.le hεξ hεξρ hεroot hβe.le hβh.le hedit
      hβgeom hrowGeom hrowGeom hξγ haLoadγ hηbalγ hrow hlevel haLoadEdit hlamβe hlamβh
      mCert Nmin M hmCert hNminN
      (by rw [hβnorm];simpa only [Nat.add_sub_cancel] using hpayload)
      (by
        dsimp [ordinarySelectedParentCertificateParameters]
        rw [hgeomEq]
        simpa only [Nat.add_sub_cancel] using hcert)
      (by simpa [ordinarySelectedParentCertificateParameters] using hbase)
      (by simpa [ordinarySelectedParentCertificateParameters] using hbudget)
      z hz
    have hrnorm:(rstar-1)+1=rstar:=by omega
    simpa only [hrnorm] using hpointwise)
  refine ⟨Q.extendedVertices 1,?_,?_⟩
  · have hsmallI:((Q.extendedVertices 1).card:ℝ)≤ε*n:=by
      simpa only [Fintype.card_fin] using marked_initial_inner_vertex_bound Q hε.le
    have hnreal:0≤(n:ℝ):=by positivity
    exact hsmallI.trans (mul_le_mul_of_nonneg_right (hεcap'.trans hεmaxCap) hnreal)
  · have hFinal:=hfailure n (by dsimp [N] at hn;omega) (Sym2 (Fin n)→Bool)
      (FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.retentionCoin (initialIndexDensity (Fin qCount) D)
        (by unfold initialIndexDensity;positivity) (by rw [←sampling.hphysical];exact sampling.hsum)))
      (fun σ=>ProtectedFactorPreparation P (retainedGraph P σ) (Q.extendedVertices 1) ξedit (aBound*aBound+aBound*bBound) F)
      (by simpa only [bprob,loss,loss0] using hTransferred)
    simp only [initialIndexDensity,Fintype.card_fin] at hFinal
    dsimp [ρ]
    apply hFinal.trans
    apply finiteLaw_probability_mono
    intro σ hPrep'
    obtain ⟨A,hA,hcard,hdecomp⟩:=hPrep'
    exact ⟨A,hA,hcard.trans (le_max_right _ _),hdecomp⟩
end Oberwolfach
