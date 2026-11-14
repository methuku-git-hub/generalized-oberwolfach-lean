module

public import Oberwolfach.FirstVortexAllClassesSynchronizedGlobal
public import Oberwolfach.FirstVortexClassPreparedBalancedHostProof
public import Oberwolfach.FirstVortexClassPreparedBalancedDegreesProof
public import Oberwolfach.LongEarlyListsResidualExtending
public import Oberwolfach.FirstVortexAllClassesSynchronizedCapacity
public import Oberwolfach.FirstVortexClassPreparedGlobalBoundaryProof
public import Oberwolfach.FirstVortexAllClassesSynchronizedSample
public import Oberwolfach.FirstVortexClassPreparedCapacityProof
public import Oberwolfach.FirstVortexClassPrepareSynchronizedSeed
public import Oberwolfach.FirstVortexClassPrepareSixTestsFixed
public import Oberwolfach.FirstVortexClassPrepareEarlyMatchingSingleLevel
public import Oberwolfach.FirstVortexClassPrepareEarlyMatching
public import Oberwolfach.LongEarlyMatchingUniformResidualInput
public import Oberwolfach.LongCapacityAutomaticMargins
public import Oberwolfach.LongFirstPrescribedAsymptotic
public import Oberwolfach.FirstVortexClassPreparedOrientedOutcome
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
local instance firstVortexAllSynchronizedBalancedDirectFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem first_vortex_all_classes_balanced_from_direct_lists
    (α lam lamAssign ε δold δlocal θ eps ξ ρ₀ bmatch ξPart δglobal ζ βfinal:ℝ) (d K r:ℕ)
    (hα:0<α) (hlam:0<lam) (hε:0<ε) (hδ:0<δold) (hθ:0<θ)
    (hρ₀:0<ρ₀) (hbmatch:0<bmatch) (hαb:(2*α)/16≤bmatch)
    (hbd:bmatch≤((ρ₀/4)/40000)/16) (hεsmall:ε≤(ρ₀/4)/80000)
    (hθδ:10*θ≤δold) (hθlocal:θ≤δold/32) (hθhi:θ≤1/100)
    (hlamlocal:lam≤δold*ε/32) (hspacing:1/(d:ℝ)≤θ/1024)
    (hd:3≤d) (hK:3≤K) (hm:7≤(r+4))
    (heps:3*eps≤lam*(θ/(100*(K:ℝ)^2))) (hξ:4*ξ≤eps/2) (hξ0:0≤ξ)
    (hρ₀1:ρ₀≤1) (hlam1:lam≤1)
    (hαsmall:(2*α)/16≤((ρ₀/4)/40000)*θ/1024)
    (hαglobal:2*α≤4*δglobal) (hδglobal:0<δglobal) (hθglobal:10*θ≤δglobal)
    (hεδ:ε≤δglobal) (hβfinal:0<βfinal) (hβfinal1:βfinal≤1) (hδbound:δglobal≤(βfinal/100)^2)
    (hdlarge:(r+4)+2≤d) (Nret:ℕ) (hNret:∀n:ℕ,Nret≤n→∀q errOrd:ℝ,
      q≤1/(((r+4):ℝ)+1)→errOrd≤θ*n→
      (n:ℝ)*q/d+(((((r+4)+1)*d-1:ℕ):ℝ))*(2*((n:ℝ)^(3/4:ℝ)/d)+ζ*n)+errOrd≤4*θ*n):
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
    (C₀:ℝ) (hC:1≤C₀) (hehi:ε≤α/(1000*C₀)) (hlamhi:lam≤α/128) (hlamθ:lam≤θ)
    (a γ ρ Δ:ℝ) (hρ0:0≤ρ) (hγ:0≤γ) (ha0:0≤a) (hγε:γ≤eps) (heps1:eps≤1)
    (ha:a≤lam/(10*d)) (hγrate:γ≤lam/(10*d))
    (hζ:ζ≤θ/4096) (hρ:ρ≤θ/4096) (hζ0:0≤ζ)
    (hscale:max a γ*n≤ρ*(Vort.extendedVertices 1).card)
    (τ Asrc BM:ℝ) (hBM:0<BM) (weight:(Fin ((r+4)+1)→Fin n)→ℝ)
    (hw:SuccessorSequenceWeightConditions P π (3*d) Dv τ Asrc BM weight)
    (BO:Fin K→ℝ) (hBO:∀i,0<BO i)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ) (hw0:∀i C,0≤w i C)
    (hwupper:∀i C,w i C≤BO i/(n:ℝ)^(longPaddedSeedExponent i))
    (z:MarkedExpandedActualOutcome (U:=U) π d) (Inner:Finset (Fin n)) (βList:ℝ)
    (hnβ:100/βfinal≤(n:ℝ)) (hnδ:2/Real.sqrt δglobal≤(n:ℝ)) (hu:Fintype.card U≤n)
    (terr τerr ξSeed ΔSeed:ℝ) (hτerr:0≤τerr) (hξSeedLe:ξSeed≤ξ) (hΔcap:Δ≤ΔSeed)
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
    ((∀v,|(((P.neighborFinset v∩Vort.extendedVertices 1).filter (fun x=>((z.1) (Sum.inl s(v,x))).1=4)).card:ℝ)-
      udens*(P.neighborFinset v∩Vort.extendedVertices 1).card|<(n:ℝ)^(3/4:ℝ)) ∧
    (∀u,
      |rawIntervalUnassignedHubCountOn π d σ u (Vort.extendedVertices 1)-
      ((Vort.extendedVertices 1).card:ℝ)*(1-(∑g,longAssignedIntervalProbability F hF K (r+4) θ u g)-
        (∑k,longAssignedSpokeProbability F hF K (r+4) θ u k))|<((Vort.extendedVertices 1).card:ℝ)^(3/4:ℝ)) ∧
    (∀v,
      |rawIntervalUnassignedColumnCount π d σ v (Vort.extendedIndices 1)-
      ∑u∈Vort.extendedIndices 1,(1-(∑g,longAssignedIntervalProbability F hF K (r+4) θ u g)-
        (∑k,longAssignedSpokeProbability F hF K (r+4) θ u k))|<((Vort.extendedVertices 1).card:ℝ)^(3/4:ℝ)) ∧
    (∀v∈Vort.extendedVertices 1,
      ((rawIntervalBoundaryHubSet π d σ (Vort.extendedIndices 1) v).card:ℝ)≤
        4*((Vort.extendedIndices 1).card:ℝ)/d+4*((Vort.extendedVertices 1).card:ℝ)^(3/4:ℝ)) ∧
    (RetainedRestrictionLocalGood π d σ false (startRetentionMinimum (rawStartHubSet π d (fun e=>rawExpandedMarkedCollapse (Sum.inr e) (z.1 (Sum.inr e))) false))
      (Vort.extendedVertices 1) (Vort.extendedIndices 1) ζ (z.2)) ∧
    (∀x y,x≠y→(5/8:ℝ)*(1/100:ℝ)^2*Fintype.card U-(n:ℝ)^(3/4:ℝ)≤
      (((Finset.univ:Finset U).filter (fun u=>rawIntervalFamilyState π d σ (x,u)=some (Sum.inr false) ∧
        rawIntervalFamilyState π d σ (y,u)=some (Sum.inr false))).card:ℝ)))→
    (∀v,((rawIntervalExtendedAnyHubSet π d σ v).card:ℝ)≤4*(Fintype.card U:ℝ)/((r+4):ℝ)+4*(n:ℝ)^(3/4:ℝ))→
    (∀u g,|rawIntervalHubStartCount π d g σ u-(n:ℝ)*longAssignedIntervalProbability F hF K (r+4) θ u g/d|<(n:ℝ)^(3/4:ℝ)/d)→
    (∀u,|(((ordinaryCommonHubSpokeRoots u).filter (fun v=>state v=true)).card:ℝ)-
      longAssignedApproxOrdinaryWeight F hF K (r+4) θ u*n|≤ξSeed*n)→
    (∀(i:Option (Fin K)) (root:LongRawHubResource n U),state root=true→
      |resourcePatternLoad (Rsrc i) (W i) (fun _ _=>true) root state-
        longAssignedMixedTarget F hF K (r+4) θ Dv p k i root|≤terr+τerr*longAssignedMixedTarget F hF K (r+4) θ Dv p k i root)→
    (∀(Del:SimpleGraph (Fin n)) (δDel:ℝ), (∀x,(Del.degree x:ℝ)≤δDel)→δDel≤ΔSeed*n→
      0≤terr+C*(δDel/(n:ℝ))+4*τerr ∧ terr+C*(δDel/(n:ℝ))+4*τerr≤eps/2)→
    (∀Del:SimpleGraph (Fin n),(∀v,(Del.degree v:ℝ)≤Δ*n)→
      LongEarlyMatchingListsForDeletion r K d θ Dv a γ eps Δ βList P π F hF weight w z Inner Del)→
    (∀Del:SimpleGraph (Fin n),(∀v,(Del.degree v:ℝ)≤Δ*n)→
      ∀u,IsExtendingList (fun x y=>rawSelectedPhysicalRelation P π d (fun e=>z.1 (Sum.inl e)) x y ∧ ¬Del.Adj x y)
        (rawReservedSpokeList π d (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (z.1 (Sum.inr e))) u \
          (Vort.extendedVertices 1∪retainedFinalMarkedAt π d (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (z.1 (Sum.inr e)))
            (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 u)) βfinal)→
    RetainedRestrictionGood π d σ false (startRetentionMinimum (rawStartHubSet π d σ false))
      (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζ z.2 →
    (∀v,((rawIntervalBoundaryHubSet π d σ Finset.univ v).card:ℝ)≤4*(Fintype.card U:ℝ)/d+4*(n:ℝ)^(3/4:ℝ)) →
    ∀Sclass:SimpleGraph (Fin n),Sclass≤P→
      (∀v,((changed ((longPhysicalStateGraph P (z.1) {0,1,2,3,4}).neighborFinset v) (Sclass.neighborFinset v)).card:ℝ)≤ξPart*n)→
    FirstVortexClassPreparedOrientedOutcomeWithBalancedDegrees P Sclass π Dv mm d (r+4) β ε Vort F hF θ lamAssign eps δlocal δglobal α bmatch ρ₀ ξ Δ a γ weight w (z.1) (startRetentionMinimum (rawStartHubSet π d (fun e=>rawExpandedMarkedCollapse (Sum.inr e) (z.1 (Sum.inr e))) false)) (z.2) :=by
  obtain ⟨Nbase,hBase⟩:=first_vortex_all_classes_global_from_synchronized_sample α lam lamAssign ε δold δlocal θ eps ξ ρ₀ bmatch ξPart δglobal ζ d K r
    hα hlam hε hδ hθ hρ₀ hbmatch hαb hbd hεsmall hθδ hθlocal hθhi hlamlocal hspacing hd hK hm heps hξ hξ0 hρ₀1 hlam1 hαsmall hαglobal hδglobal hθglobal hdlarge Nret hNret
  refine ⟨max Nbase 1,?_⟩
  intro n hn _ U _ _ P π Dv mm β Vort hreg hDv hρhi hρlo hDlo hDhi hmm F hF Allowed hAllowed hclass hcut hcutHost hnoshort C₀ hC hehi hlamhi hlamθ a γ ρ Δ hρ0 hγ ha0 hγε heps1 ha hγrate hζ hρ hζ0 hscale τ Asrc BM hBM weight hw BO hBO w hw0 hwupper z Inner βList hnβ hnδ hu terr τerr ξSeed ΔSeed hτerr hξSeedLe hΔcap hξdeg hξedges hmargin raw σ ni hni ℓ p k udens pstar BMseed BOseed C Wm Wo W Rsrc R state hub hSix hboundaryGlobal hstarts hcountSeed hload hbudgetSeed hEarly hExt hRetentionGlobal hBoundaryAll Sclass hSP hedit
  have hPrep:=hBase n (by omega) U P π Dv mm β Vort hreg hDv hρhi hρlo hDlo hDhi hmm F hF Allowed hAllowed hclass hcut hcutHost hnoshort C₀ hC hehi hlamhi hlamθ a γ ρ Δ hρ0 hγ ha0 hγε heps1 ha hγrate hζ hρ hζ0 hscale τ Asrc BM hBM weight hw BO hBO w hw0 hwupper z Inner βList terr τerr ξSeed ΔSeed hτerr hξSeedLe hΔcap hξdeg hξedges hmargin hSix hboundaryGlobal hstarts hcountSeed hload hbudgetSeed hEarly hRetentionGlobal hBoundaryAll Sclass hSP hedit
  have hBalanced:=first_vortex_class_prepared_balanced_host_completion P Sclass π Dv mm d (r+4) β ε Vort F hF θ lamAssign eps δlocal δglobal α bmatch ρ₀ ξ Δ a γ βfinal weight w z.1 _ z.2 hρ₀ hbmatch.le hbd hαb hθglobal hεδ hβfinal hβfinal1 hδglobal hδbound hSP (by omega) hnβ hnδ hu hExt hPrep
  exact first_vortex_class_prepared_balanced_degrees P Sclass π Dv mm d (r+4) β ε Vort F hF θ lamAssign eps δlocal δglobal α bmatch ρ₀ ξ Δ a γ weight w z.1 _ z.2 (by omega) hnoshort hSP hBalanced
end Oberwolfach
