module

public import Oberwolfach.LongEveryClassValidDeletionEvent
public import Oberwolfach.FirstVortexAllClassesSameDeletion
public import Oberwolfach.LongEveryClassPreparedSameDeletion
public import Oberwolfach.FirstVortexAllClassesSynchronizedSample
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
local instance firstVortexAllCorrectionSameSampleFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem first_vortex_all_classes_correction_matching_same_sample
    (α lam lamAssign ε δold δlocal θ eps ξ ρ₀ bmatch ξPart:ℝ) (d K r:ℕ)
    (hα:0<α) (hlam:0<lam) (hε:0<ε) (hδ:0<δold) (hθ:0<θ)
    (hρ₀:0<ρ₀) (hbmatch:0<bmatch) (hαb:(2*α)/16≤bmatch)
    (hbd:bmatch≤((ρ₀/4)/40000)/16) (hεsmall:ε≤(ρ₀/4)/80000)
    (hθδ:10*θ≤δold) (hθlocal:θ≤δold/32) (hθhi:θ≤1/100)
    (hlamlocal:lam≤δold*ε/32) (hspacing:1/(d:ℝ)≤θ/1024)
    (hd:3≤d) (hK:3≤K) (hm:7≤(r+4))
    (heps:3*eps≤lam*(θ/(100*(K:ℝ)^2))) (hξ:4*ξ≤eps/2) (hξ0:0≤ξ):
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
    (a γ ζ ρ Δ:ℝ) (hγ:0≤γ) (ha0:0≤a) (hγε:γ≤eps) (heps1:eps≤1)
    (ha:a≤lam/(10*d)) (hγrate:γ≤lam/(10*d))
    (hζ:ζ≤θ/4096) (hρ:ρ≤θ/4096) (hζ0:0≤ζ)
    (hscale:max a γ*n≤ρ*(Vort.extendedVertices 1).card)
    (τ Asrc BM:ℝ) (hBM:0<BM) (weight:(Fin ((r+4)+1)→Fin n)→ℝ)
    (hw:SuccessorSequenceWeightConditions P π (3*d) Dv τ Asrc BM weight)
    (BO:Fin K→ℝ) (hBO:∀i,0<BO i)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ) (hw0:∀i C,0≤w i C)
    (hwupper:∀i C,w i C≤BO i/(n:ℝ)^(longPaddedSeedExponent i))
    (z:MarkedExpandedActualOutcome (U:=U) π d) (Inner:Finset (Fin n)) (βList:ℝ)
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
    ∀(γLoss σLoss:ℝ) (D₀:MarkedReferenceDeletion P π d (fun e=>rawExpandedMarkedCollapse e (z.1 e))),
    let σSelected:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (z.1 e)
    let H:=retainedRawMarkedSpokes π d (fun e=>σSelected (Sum.inr e)) false
      (startRetentionMinimum (rawStartHubSet π d (fun e=>σSelected (Sum.inr e)) false)) z.2 false false
    let σ':=rawMarkedDeleteRims σSelected (markedSampleArcSetGraph P π d σSelected D₀.arcs).edgeFinset
    let E':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true;
    ∀(B:ℕ) (CReserve:MarkedSupportedEdgeSet (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) π U), Δ≤ξ →
    D₀.Valid H (r+4) (Vort.extendedVertices 1) (Vort.extendedIndices 1) (γLoss*n) (σLoss*n) →
    CReserve.edges.card≤B → Disjoint D₀.removed CReserve.edges →
    LongEveryClassValidDeletionEvent Δ P π d r γLoss σLoss ξPart z (Vort.extendedVertices 1) (Vort.extendedIndices 1)
      K B θ Dv a γ eps βList F hF weight w →
    ∀Sclass:SimpleGraph (Fin n),Sclass≤P→Sclass.IsRegularOfDegree (2*Fintype.card U)→
      (∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (Sclass.neighborFinset v)).card:ℝ)≤ξPart*n)→
      (∀x∈Vort.extendedVertices 1,∀y∈Vort.extendedVertices 1,Sclass.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y)→
      markedResourceRimGraph CReserve.edges≤Sclass→
      (∀x∈Vort.extendedVertices 1,∀y∈Vort.extendedVertices 1,(longSelectedPhysicalGraph P π d z.1).Adj x y→Sclass.Adj x y) ∧
      ∃M:Fin n→Fin n→ℕ,∃Del:SimpleGraph (Fin n),
        LongClassMatchingDeletionWitness Δ P π d r z (Vort.extendedVertices 1) K θ Dv a γ eps βList F hF weight w D₀ CReserve.edges Sclass M Del ∧
        FirstVortexClassPreparedAtDeletion P Sclass π Dv mm d (r+4) β ε Vort F hF θ lamAssign eps δlocal α bmatch ρ₀ ξ Δ a γ weight w z.1
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 Del :=by
  obtain ⟨N,hBase⟩:=first_vortex_all_classes_prepare_from_synchronized_sample α lam lamAssign ε δold δlocal θ eps ξ ρ₀ bmatch ξPart d K r
    hα hlam hε hδ hθ hρ₀ hbmatch hαb hbd hεsmall hθδ hθlocal hθhi hlamlocal hspacing hd hK hm heps hξ hξ0
  refine ⟨N,?_⟩
  intro n hn _ U _ _ P π Dv mm β Vort hreg hDv hρhi hρlo hDlo hDhi hmm F hF Allowed hAllowed hclass hcut hcutHost hnoshort C₀ hC hehi hlamhi hlamθ a γ ζ ρ Δ hγ ha0 hγε heps1 ha hγrate hζ hρ hζ0 hscale τ Asrc BM hBM weight hw BO hBO w hw0 hwupper z Inner βList terr τerr ξSeed ΔSeed hτerr hξSeedLe hΔcap hξdeg hξedges hmargin raw σ ni hni ℓ p k udens pstar BMseed BOseed C Wm Wo W Rsrc R state hub hSix hboundaryGlobal hstarts hcountSeed hload hbudgetSeed hEarly γLoss σLoss D₀ σSelected H σ' E' K' B CReserve hΔξ hValid hBound hDisjoint hEvent
  have hClass:=hEvent D₀ hValid CReserve hBound hDisjoint
  have hAll:=hBase n hn U P π Dv mm β Vort hreg hDv hρhi hρlo hDlo hDhi hmm F hF Allowed hAllowed hclass hcut hcutHost hnoshort C₀ hC hehi hlamhi hlamθ a γ ζ ρ Δ hγ ha0 hγε heps1 ha hγrate hζ hρ hζ0 hscale τ Asrc BM hBM weight hw BO hBO w hw0 hwupper z Inner βList terr τerr ξSeed ΔSeed hτerr hξSeedLe hΔcap hξdeg hξedges hmargin hSix hboundaryGlobal hstarts hcountSeed hload hbudgetSeed hEarly
  apply long_every_class_prepared_same_deletion P π d r Dv mm β ε Vort γLoss σLoss ξPart z θ lamAssign eps δlocal α bmatch ρ₀ ξ Δ a γ βList F hF weight w D₀ CReserve.edges hΔξ hClass
  intro S hSP hregS hedit hinner hreserve
  exact hAll S hSP hedit
end Oberwolfach
