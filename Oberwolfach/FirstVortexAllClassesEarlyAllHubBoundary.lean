module

public import Oberwolfach.FirstVortexPreparedAllHubFromCommonBoundary
public import Oberwolfach.FirstVortexPreparedAllHubFromCommonPrecise
public import Oberwolfach.MarkedResourceRimGraph
public import Oberwolfach.FirstVortexRetainedSingleLevelToGlobal
public import Oberwolfach.FirstVortexClassRetainedFullPackingEarlySingleLevel
public import Oberwolfach.FirstVortexClassPreparedRetainedFullPackingOutcome
public import Oberwolfach.FirstVortexClassProtectedFullPackingFromRetainedTests
public import Oberwolfach.FirstVortexClassPreparedRetainedFullPackingOutcome
public import Oberwolfach.FirstVortexClassPrepareEarlyMatching
public import Oberwolfach.LongEarlyMatchingUniformResidualInput
public import Oberwolfach.LongCapacityAutomaticMargins
public import Oberwolfach.LongFirstPrescribedAsymptotic
public import Oberwolfach.FirstVortexClassPreparedRetainedFullPackingOutcome
public import Oberwolfach.FirstVortexClassSourceFromRetainedTests
public import Oberwolfach.FirstVortexPreparedOrientedOutcome
public import Oberwolfach.FirstVortexOrientedAutomaticCoefficients
public import Oberwolfach.FirstVortexPreparedOrientedOutcome
public import Oberwolfach.FirstVortexProtectedAutomaticCoefficients
public import Oberwolfach.FirstVortexPreparedOrientedOutcome

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 80000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance firstVortexAllClassesAllHubBoundaryFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem first_vortex_all_classes_single_level_early_all_hub_boundary
    (α lam lamAssign ε δold δlocal δglobal θ eps ξ ρ₀ bmatch ξPart ζret:ℝ) (d K r:ℕ)
    (hα:0<α) (hlam:0<lam) (hε:0<ε) (hδ:0<δold) (hθ:0<θ)
    (hρ₀:0<ρ₀) (hbmatch:0<bmatch) (hαb:(2*α)/16≤bmatch)
    (hbd:bmatch≤((ρ₀/4)/40000)/16) (hεsmall:ε≤(ρ₀/4)/80000)
    (hθδ:10*θ≤δold) (hθlocal:θ≤δold/32) (hθhi:θ≤1/100)
    (hlamlocal:lam≤δold*ε/32) (hspacing:1/(d:ℝ)≤θ/1024)
    (hd:3≤d) (hK:3≤K) (hm:7≤(r+4))
    (heps:3*eps≤lam*(θ/(100*(K:ℝ)^2))) (hξ:4*ξ≤eps/2) (hξ0:0≤ξ)
    (hρ₀hi:ρ₀≤1) (hδglobal:0<δglobal) (hθglobal:10*θ≤δglobal)
    (hprecise:ε≤((ρ₀/4)/40000)/8192) (hsmall:lam+ξPart≤((ρ₀/4)/40000)*θ/4096)
    (hlamθ:lam≤θ) (hdlarge:(r+4)+2≤d)
    (Nret:ℕ) (hNret:∀n:ℕ,Nret≤n→∀q errOrd:ℝ,
      q≤1/((((r+4):ℕ):ℝ)+1)→errOrd≤θ*n→
      (n:ℝ)*q/d+(((((r+4)+1)*d-1:ℕ):ℝ))*(2*((n:ℝ)^(3/4:ℝ)/d)+ζret*n)+errOrd≤4*θ*n):
    ∃N:ℕ,∀n:ℕ,N≤n→∀ [Nonempty (Fin n)] (U:Type) [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (Dv mm:ℕ) (β:ℝ) (Vort:Vortex U P Dv β ε mm)
    (hreg:P.IsRegularOfDegree Dv) (hDv:0<Dv) (hρhi:initialIndexDensity U Dv≤1)
    (hρlo:ρ₀ ≤ initialIndexDensity U Dv) (hDlo:(n:ℝ)/2≤Dv) (hDhi:(Dv:ℝ)≤2*n) (hmm:0<mm)
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (hclass:∀u,factorPreparationClass (F u) K=none)
    (hcut:(1/(((r+4):ℝ)+1))/(d:ℝ)≤θ)
    (hcutHost:5/((((r+4):ℝ)+1)*(d:ℝ)+5)+(((r+4):ℝ)+1)*(d:ℝ)/(K:ℝ)≤θ/2)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (C₀:ℝ) (hC:1≤C₀) (hehi:ε≤α/(1000*C₀)) (hlamhi:lam≤α/128)
    (a γ ρ Δ:ℝ) (hγ:0≤γ) (ha0:0≤a) (hγε:γ≤eps) (heps1:eps≤1)
    (ha:a≤lam/(10*d)) (hγrate:γ≤lam/(10*d))
    (hζ:ζret≤θ/4096) (hρ:ρ≤θ/4096) (hζ0:0≤ζret) (hρ0:0≤ρ)
    (hscale:max a γ*n≤ρ*(Vort.extendedVertices 1).card)
    (hmax:2*max a (4*γ)≤lam/3) (hΔlam:Δ≤lam/3)
    (τ Asrc BM:ℝ) (hBM:0<BM) (weight:(Fin ((r+4)+1)→Fin n)→ℝ)
    (hw:SuccessorSequenceWeightConditions P π (3*d) Dv τ Asrc BM weight)
    (BO:Fin K→ℝ) (hBO:∀i,0<BO i)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ) (hw0:∀i C,0≤w i C)
    (hwupper:∀i C,w i C≤BO i/(n:ℝ)^(longPaddedSeedExponent i))
    (z:MarkedExpandedActualOutcome (U:=U) π d) (Inner:Finset (Fin n)) (βList:ℝ)
    (terr τerr:ℝ) (hτerr:0≤τerr)
    (hξdeg:ξPart≤(2*α)/32) (hξedges:ξPart/2≤(lamAssign-lam)*ε)
    (hmargin:ξPart*n≤(δlocal-δold)*((Vort.extendedVertices 1).card:ℝ)),
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e ((z.1) e)
    let σ:=fun e=>raw (Sum.inr e)
    let ni:=@longPaddedSeedExponent K
    let hni:=@long_padded_seed_exponent_positive K
    let ℓ:=fun i=>ni i+2
    let p:=(∑u,longAssignedApproxOrdinaryWeight F hF K (r+4) θ u)/(Dv:ℝ)
    let k:=(∑u,longAssignedApproxMarkedWeight F hF K (r+4) θ u)/(Dv:ℝ)
    let udens:=2*(∑u,(1-(1/100:ℝ)-(1/100:ℝ)/((r+4):ℝ)-longAssignedApproxMarkedWeight F hF K (r+4) θ u-longAssignedApproxOrdinaryWeight F hF K (r+4) θ u))/(Dv:ℝ)
    let pstar:=min (1/4:ℝ) (min (ρ₀/8) (ρ₀/(6*(((r+4):ℝ)+1))))
    let BMseed:=2*BM/pstar^(2*(r+4)+1)
    let BOseed:=fun i=>2*BO i/pstar^(2*(ni i+2))
    let C:=10*((((r+4):ℝ)+1)^4*BMseed+∑i:Fin K,((ni i:ℝ)+2)^4*BOseed i)
    let Wm:=longAssignedMarkedSeed F hF K (r+4) d θ Dv π weight
    let Wo:=longAssignedOrdinarySeed F hF K (r+4) d θ Dv P π ni hni w
    let W:=longMixedSeedWeight Wm Wo
    let Rsrc:=longRawHubResources (U:=U) π d (r+4) ℓ
    let R:=mixedCandidateResources Rsrc
    let state:=longRawHubState P π d raw true true
    let hub:=longRawHubNames (U:=U) π d (r+4) ℓ
    (0≤udens ∧ udens≤2*θ)→
    (∀w,|rawIntervalUnassignedHubCountOn π d σ w (Vort.extendedVertices 1)-
      ((Vort.extendedVertices 1).card:ℝ)*(1-(∑g,longAssignedIntervalProbability F hF K (r+4) θ w g)-
        (∑j,longAssignedSpokeProbability F hF K (r+4) θ w j))|<(n:ℝ)^(3/4:ℝ))→
    (∀v,|rawIntervalUnassignedColumnCount π d σ v Finset.univ-
      ∑w:U,(1-(∑g,longAssignedIntervalProbability F hF K (r+4) θ w g)-
        (∑j,longAssignedSpokeProbability F hF K (r+4) θ w j))|<(n:ℝ)^(3/4:ℝ))→
    (∀v,|(((P.neighborFinset v∩Vort.extendedVertices 1).filter (fun x=>((z.1) (Sum.inl s(v,x))).1=4)).card:ℝ)-
      udens*(P.neighborFinset v∩Vort.extendedVertices 1).card|<(n:ℝ)^(3/4:ℝ))→
    (∀u∈Vort.extendedIndices 1,
      |rawIntervalUnassignedHubCountOn π d σ u (Vort.extendedVertices 1)-
      ((Vort.extendedVertices 1).card:ℝ)*(1-(∑g,longAssignedIntervalProbability F hF K (r+4) θ u g)-
        (∑k,longAssignedSpokeProbability F hF K (r+4) θ u k))|<((Vort.extendedVertices 1).card:ℝ)^(3/4:ℝ))→
    (∀v∈Vort.extendedVertices 1,
      |rawIntervalUnassignedColumnCount π d σ v (Vort.extendedIndices 1)-
      ∑u∈Vort.extendedIndices 1,(1-(∑g,longAssignedIntervalProbability F hF K (r+4) θ u g)-
        (∑k,longAssignedSpokeProbability F hF K (r+4) θ u k))|<((Vort.extendedVertices 1).card:ℝ)^(3/4:ℝ))→
    (∀v∈Vort.extendedVertices 1,
      ((rawIntervalBoundaryHubSet π d σ (Vort.extendedIndices 1) v).card:ℝ)≤
        4*((Vort.extendedIndices 1).card:ℝ)/d+4*((Vort.extendedVertices 1).card:ℝ)^(3/4:ℝ))→
    RetainedRestrictionLocalGood π d σ false (startRetentionMinimum (rawStartHubSet π d (fun e=>rawExpandedMarkedCollapse (Sum.inr e) (z.1 (Sum.inr e))) false))
      (Vort.extendedVertices 1) (Vort.extendedIndices 1) ζret (z.2)→
    (∀x y,x≠y→(5/8:ℝ)*(1/100:ℝ)^2*Fintype.card U-(n:ℝ)^(3/4:ℝ)≤
      (((Finset.univ:Finset U).filter (fun u=>rawIntervalFamilyState π d σ (x,u)=some (Sum.inr false) ∧
        rawIntervalFamilyState π d σ (y,u)=some (Sum.inr false))).card:ℝ))→
    (∀v,((rawIntervalExtendedAnyHubSet π d σ v).card:ℝ)≤4*(Fintype.card U:ℝ)/((r+4):ℝ)+4*(n:ℝ)^(3/4:ℝ))→
    (∀u g,|rawIntervalHubStartCount π d g σ u-(n:ℝ)*longAssignedIntervalProbability F hF K (r+4) θ u g/d|<(n:ℝ)^(3/4:ℝ)/d)→
    (∀u,|(((ordinaryCommonHubSpokeRoots u).filter (fun v=>state v=true)).card:ℝ)-
      longAssignedApproxOrdinaryWeight F hF K (r+4) θ u*n|≤ξ*n)→
    (∀(i:Option (Fin K)) (root:LongRawHubResource n U),state root=true→
      |resourcePatternLoad (Rsrc i) (W i) (fun _ _=>true) root state-
        longAssignedMixedTarget F hF K (r+4) θ Dv p k i root|≤terr+τerr*longAssignedMixedTarget F hF K (r+4) θ Dv p k i root)→
    (∀(Del:SimpleGraph (Fin n)) (δDel:ℝ), (∀x,(Del.degree x:ℝ)≤δDel)→δDel≤Δ*n→
      0≤terr+C*(δDel/(n:ℝ))+4*τerr ∧ terr+C*(δDel/(n:ℝ))+4*τerr≤eps/2)→
    RetainedRestrictionGood π d σ false (startRetentionMinimum (rawStartHubSet π d (fun e=>rawExpandedMarkedCollapse (Sum.inr e) (z.1 (Sum.inr e))) false))
      (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζret z.2→
    (∀v,((rawIntervalBoundaryHubSet π d σ Finset.univ v).card:ℝ)≤4*(Fintype.card U:ℝ)/d+4*(n:ℝ)^(3/4:ℝ))→
    (∀Del:SimpleGraph (Fin n),(∀v,(Del.degree v:ℝ)≤Δ*n)→
      LongEarlyMatchingListsForDeletion r K d θ Dv a γ eps Δ βList P π F hF weight w z Inner Del)→
    ∀Sclass:SimpleGraph (Fin n),Sclass≤P→Sclass.IsRegularOfDegree (2*Fintype.card U)→
      (∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (Sclass.neighborFinset v)).card:ℝ)≤ξPart*n)→
      (∀x∈Vort.extendedVertices 1,∀y∈Vort.extendedVertices 1,Sclass.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y)→
    FirstVortexClassPreparedRetainedFullPackingOutcomeWithAllHubLoad P Sclass π Dv mm d (r+4) β ε Vort F hF θ lamAssign eps δlocal δglobal α bmatch ρ₀ ξ Δ a γ weight w (z.1) (startRetentionMinimum (rawStartHubSet π d (fun e=>rawExpandedMarkedCollapse (Sum.inr e) (z.1 (Sum.inr e))) false)) (z.2) :=by
  obtain ⟨Nfirst,hFirst⟩:=first_vortex_class_full_packing_from_early_matching_single_level_retained α lam lamAssign ε δold δlocal θ eps ξ ρ₀ bmatch ξPart d K r
    hα hlam hε hδ hθ hρ₀ hbmatch hαb hbd hεsmall hθδ hθlocal hθhi hlamlocal hspacing hd hK hm heps hξ hξ0
  obtain ⟨Nglobal,hGlobal⟩:=first_vortex_class_prepared_all_hub_from_common_boundary ε θ δglobal ρ₀ lam lamAssign ζret α ξPart (r+4) d
    (by omega) hdlarge hε hθ (by linarith) hδglobal hθglobal Nret hNret hρ₀hi hεsmall hlam.le hlam (by linarith) (by omega) hspacing hα hρ₀ hθhi hsmall hprecise hlamθ
  refine ⟨max Nfirst Nglobal,?_⟩
  intro n hn _ U _ _ P π Dv mm β Vort hreg hDv hρhi hρlo hDlo hDhi hmm F hF Allowed hAllowed hclass hcut hcutHost hnoshort
    C₀ hC hehi hlamhi a γ ρ Δ hγ ha0 hγε heps1 ha hγrate hζ hρ hζ0 hρ0 hscale hmax hΔlam τ Asrc BM hBM weight hw BO hBO w hw0 hwupper z Inner βList terr τerr hτerr
    hξdeg hξedges hmargin raw σ ni hni ℓ p k udens pstar BMseed BOseed C Wm Wo W Rsrc R state hub hudens hfixedAll hcolumnAll hrow hfixed hcolumn hboundary hrows hpair hboundaryGlobal hstarts hcount hload hbudget hgood hbound hEarly Sclass hSP hregS hedit hinner
  have heps0:0≤eps:=by linarith
  have hFirst':=hFirst n (by omega)
  have hGlobal':=hGlobal n K (by omega) hK
  have hd1:firstVortexClassFullPackingSingleMatchingFinRetained n=firstVortexAllClassesAllHubBoundaryFin n:=Subsingleton.elim _ _
  have hd2:firstVortexPreparedAllHubBoundaryAssembledFin n=firstVortexAllClassesAllHubBoundaryFin n:=Subsingleton.elim _ _
  have hd1K:firstVortexClassFullPackingSingleMatchingFinRetained K=firstVortexAllClassesAllHubBoundaryFin K:=Subsingleton.elim _ _
  have hd2K:firstVortexPreparedAllHubBoundaryAssembledFin K=firstVortexAllClassesAllHubBoundaryFin K:=Subsingleton.elim _ _
  try rw [hd1] at hFirst'
  try rw [hd1K] at hFirst'
  try rw [hd2] at hGlobal'
  try rw [hd2K] at hGlobal'
  have hbase:=hFirst' U P Sclass π Dv mm β Vort hreg hDv hρhi hρlo hDlo hDhi hmm F hF Allowed hAllowed hclass hcut hcutHost hnoshort
    C₀ hC hehi hlamhi hlamθ a γ ζret ρ Δ hγ ha0 hγε heps1 ha hγrate hζ hρ hζ0 hscale τ Asrc BM hBM weight hw BO hBO w hw0 hwupper z Inner βList terr τerr hτerr hSP hedit hξdeg hξedges hmargin
    hrow hfixed hcolumn hboundary hrows hpair hboundaryGlobal hstarts hcount hload hbudget hEarly
  have hn0:0<n:=by have hh:=Fintype.card_pos (α:=Fin n); simpa only [Fintype.card_fin] using hh
  have hUle:Fintype.card U≤n:=first_vortex_hub_cardinality_le_host hreg hn0 hDv hρhi
  exact hGlobal' U P Sclass π Dv mm β Vort hreg hDv hρhi hmm F hF δlocal bmatch eps ξ Δ a γ ρ
    heps0 heps C₀ udens hC hehi hlamhi hudens.1 hudens.2 hUle hmax hΔlam hSP hγ ha hγrate hζ hζ0 hρ hρ0 hscale hnoshort weight w z.1
    hedit (by intro v hv; exact hrow v)
    (startRetentionMinimum (rawStartHubSet π d (fun e=>rawExpandedMarkedCollapse (Sum.inr e) (z.1 (Sum.inr e))) false)) z.2
    hrows hfixed hcolumn hbound hstarts hgood hfixedAll hcolumnAll hbase
end Oberwolfach
