module

public import Oberwolfach.FirstVortexPreparedCommonOutcome

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance firstVortexPrepareCommonTestsFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem first_vortex_prepare_from_common_tests
    (α lam ε δlocal θ eps ξ ρ₀ bmatch:ℝ) (d K m:ℕ)
    (hα:0<α) (hlam:0<lam) (hε:0<ε) (hδ:0<δlocal) (hθ:0<θ)
    (hρ₀:0<ρ₀) (hbmatch:0<bmatch) (hαb:α/16≤bmatch)
    (hbd:bmatch≤((ρ₀/4)/40000)/16) (hmarg:4/(m:ℝ)≤bmatch/2) (hεsmall:ε≤(ρ₀/4)/80000)
    (hθδ:10*θ≤δlocal) (hθlocal:θ≤δlocal/32) (hθhi:θ≤1/100)
    (hlamlocal:lam≤δlocal*ε/32) (hspacing:1/(d:ℝ)≤θ/1024)
    (hd:3≤d) (hK:3≤K) (hm:7≤m)
    (heps:3*eps≤lam*(θ/(100*(K:ℝ)^2))) (hξ:4*ξ≤eps/2) (hξ0:0≤ξ):
    ∃N:ℕ,∀n:ℕ,N≤n→∀(U:Type) [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (Dv mm:ℕ) (β:ℝ) (Vort:Vortex U P Dv β ε mm)
    (hreg:P.IsRegularOfDegree Dv) (hDv:0<Dv) (hρhi:initialIndexDensity U Dv≤1)
    (hρlo:ρ₀ ≤ initialIndexDensity U Dv) (hDlo:(n:ℝ)/2≤Dv) (hDhi:(Dv:ℝ)≤2*n) (hmm:0<mm)
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (hclass:∀u,factorPreparationClass (F u) K=none)
    (hcut:(1/((m:ℝ)+1))/(d:ℝ)≤θ)
    (hcutHost:5/(((m:ℝ)+1)*(d:ℝ)+5)+((m:ℝ)+1)*(d:ℝ)/(K:ℝ)≤θ/2)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (C₀:ℝ) (hC:1≤C₀) (hehi:ε≤α/(1000*C₀)) (hlamhi:lam≤α/128) (hlamθ:lam≤θ)
    (a γ ζ ρ Δ:ℝ) (hγ:0≤γ) (hγε:γ≤eps) (heps1:eps≤1)
    (ha:a≤lam/(10*d)) (hγrate:γ≤lam/(10*d))
    (hζ:ζ≤θ/4096) (hρ:ρ≤θ/4096) (hζ0:0≤ζ)
    (hscale:max a γ*n≤ρ*(Vort.extendedVertices 1).card)
    (τ Asrc BM:ℝ) (hBM:0<BM) (weight:(Fin (m+1)→Fin n)→ℝ)
    (hw:SuccessorSequenceWeightConditions P π (3*d) Dv τ Asrc BM weight)
    (BO:Fin K→ℝ) (hBO:∀i,0<BO i)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ) (hw0:∀i C,0≤w i C)
    (hwupper:∀i C,w i C≤BO i/(n:ℝ)^(longPaddedSeedExponent i))
    (σE:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d
      (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (σE (Sum.inr e))) false) t)
    (terr τerr:ℝ) (hτerr:0≤τerr),
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σE e)
    let σ:=fun e=>raw (Sum.inr e)
    let ni:=@longPaddedSeedExponent K
    let hni:=@long_padded_seed_exponent_positive K
    let ℓ:=fun i=>ni i+2
    let p:=(∑u,longAssignedApproxOrdinaryWeight F hF K m θ u)/(Dv:ℝ)
    let k:=(∑u,longAssignedApproxMarkedWeight F hF K m θ u)/(Dv:ℝ)
    let udens:=2*(∑u,(1-(1/100:ℝ)-(1/100:ℝ)/(m:ℝ)-longAssignedApproxMarkedWeight F hF K m θ u-longAssignedApproxOrdinaryWeight F hF K m θ u))/(Dv:ℝ)
    let pstar:=min (1/4:ℝ) (min (ρ₀/8) (ρ₀/(6*((m:ℝ)+1))))
    let BMseed:=2*BM/pstar^(2*m+1)
    let BOseed:=fun i=>2*BO i/pstar^(2*(ni i+2))
    let C:=10*(((m:ℝ)+1)^4*BMseed+∑i:Fin K,((ni i:ℝ)+2)^4*BOseed i)
    let Wm:=longAssignedMarkedSeed F hF K m d θ Dv π weight
    let Wo:=longAssignedOrdinarySeed F hF K m d θ Dv P π ni hni w
    let W:=longMixedSeedWeight Wm Wo
    let Rsrc:=longRawHubResources (U:=U) π d m ℓ
    let R:=mixedCandidateResources Rsrc
    let state:=longRawHubState P π d raw true true
    let hub:=longRawHubNames (U:=U) π d m ℓ
    (∀v,|(((P.neighborFinset v∩Vort.extendedVertices 1).filter (fun x=>(σE (Sum.inl s(v,x))).1=4)).card:ℝ)-
      udens*(P.neighborFinset v∩Vort.extendedVertices 1).card|<(n:ℝ)^(3/4:ℝ))→
    (∀j∈Finset.Icc 1 Vort.length,∀u∈Vort.extendedIndices j,
      |rawIntervalUnassignedHubCountOn π d σ u (Vort.extendedVertices j)-
      ((Vort.extendedVertices j).card:ℝ)*(1-(∑g,longAssignedIntervalProbability F hF K m θ u g)-
        (∑k,longAssignedSpokeProbability F hF K m θ u k))|<((Vort.extendedVertices j).card:ℝ)^(3/4:ℝ))→
    (∀j∈Finset.Icc 1 Vort.length,∀v∈Vort.extendedVertices j,
      |rawIntervalUnassignedColumnCount π d σ v (Vort.extendedIndices j)-
      ∑u∈Vort.extendedIndices j,(1-(∑g,longAssignedIntervalProbability F hF K m θ u g)-
        (∑k,longAssignedSpokeProbability F hF K m θ u k))|<((Vort.extendedVertices j).card:ℝ)^(3/4:ℝ))→
    (∀j∈Finset.Icc 1 Vort.length,∀v∈Vort.extendedVertices j,
      ((rawIntervalBoundaryHubSet π d σ (Vort.extendedIndices j) v).card:ℝ)≤
        4*((Vort.extendedIndices j).card:ℝ)/d+4*((Vort.extendedVertices j).card:ℝ)^(3/4:ℝ))→
    (∀j∈Finset.Icc 1 Vort.length,RetainedRestrictionLocalGood π d σ false t
      (Vort.extendedVertices j) (Vort.extendedIndices j) ζ Jret)→
    (∀x y,x≠y→(5/8:ℝ)*(1/100:ℝ)^2*Fintype.card U-(n:ℝ)^(3/4:ℝ)≤
      (((Finset.univ:Finset U).filter (fun u=>rawIntervalFamilyState π d σ (x,u)=some (Sum.inr false) ∧
        rawIntervalFamilyState π d σ (y,u)=some (Sum.inr false))).card:ℝ))→
    (∀v,((rawIntervalExtendedAnyHubSet π d σ v).card:ℝ)≤4*(Fintype.card U:ℝ)/(m:ℝ)+4*(n:ℝ)^(3/4:ℝ))→
    (∀u g,|rawIntervalHubStartCount π d g σ u-(n:ℝ)*longAssignedIntervalProbability F hF K m θ u g/d|<(n:ℝ)^(3/4:ℝ)/d)→
    (∀u,|(((ordinaryCommonHubSpokeRoots u).filter (fun v=>state v=true)).card:ℝ)-
      longAssignedApproxOrdinaryWeight F hF K m θ u*n|≤ξ*n)→
    (∀(i:Option (Fin K)) (root:LongRawHubResource n U),state root=true→
      |resourcePatternLoad (Rsrc i) (W i) (fun _ _=>true) root state-
        longAssignedMixedTarget F hF K m θ Dv p k i root|≤terr+τerr*longAssignedMixedTarget F hF K m θ Dv p k i root)→
    (∀(Del:SimpleGraph (Fin n)) (δDel:ℝ), (∀x,(Del.degree x:ℝ)≤δDel)→δDel≤Δ*n→
      0≤terr+C*(δDel/(n:ℝ))+4*τerr ∧ terr+C*(δDel/(n:ℝ))+4*τerr≤eps/2)→
    (∀(Del:SimpleGraph (Fin n)) (δDel:ℝ), (∀x,(Del.degree x:ℝ)≤δDel)→δDel≤Δ*n→
      let S:=longRawSurvivingResources P π d raw true true Del.edgeFinset
      let e:{v // v∈S}↪_:=Function.Embedding.subtype _
      let T:=bernoulliVertexSet state
      let q:=survivingCandidateEmbedding R S T (long_raw_surviving_resources_subset P π d raw true true Del.edgeFinset)
      let selected:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (σE e)
      let Hret:=retainedRawMarkedSpokes π d σ false t Jret false false
      let Q:=restrictedResourceSet R e
      ∃M:Finset (RestrictedResource R e),
        (∀c∈M,0<mixedCandidateWeight W c.val) ∧
        (∀c∈M,∀c'∈M,c≠c'→Disjoint (Q c) (Q c')) ∧
        (∀i,((longRawIncidenceSet S i\M.biUnion Q).card:ℝ)≤max (a*n) (γ*(longRawIncidenceSet S i).card)) ∧
        (∀z:LongRetainedHubTest F hF K θ,
          let test:=longRetainedHubIndicator F hF θ hub z
          let mass:=∑c:RestrictedResource R e,test c.val*mixedCandidateWeight W c.val
          (1-γ)*mass≤∑c∈M,test c.val) ∧
        (∀z:LongRetainedHubTest F hF K θ,
          let test:=longRetainedHubIndicator F hF θ hub z
          let mass:=∑c:RestrictedResource R e,test c.val*mixedCandidateWeight W c.val
          (∑c∈M,test c.val)≤(1+γ)*mass) ∧
        (∀(Reserve:Finset (Finset (Fin n)⊕(Fin n×U))) (X:Finset (Fin n)) (Z:Finset U),
          MarkedFixedTerminalAbsorber P π d m selected Hret Reserve X Z →
          LongMatchingSourceCountWitness F hF π d m ℓ θ eps T (M.map q)))→
    FirstVortexPreparedCommonOutcome P π Dv mm d m β ε Vort F hF θ lam eps δlocal α bmatch ρ₀ ξ Δ a γ weight w σE t Jret :=by
  obtain ⟨N,hN⟩:=first_vortex_all_level_source_matching_with_automatic_coefficients α lam ε δlocal θ eps ξ ρ₀ bmatch d K m hα hlam hε hδ hθ hρ₀ hbmatch hαb hbd hmarg hεsmall hθδ hθlocal hθhi hlamlocal hspacing hd (by omega) (by omega) heps hξ hξ0
  refine ⟨N,?_⟩
  intro n hn U _ _ P π Dv mm β Vort hreg hDv hρhi hρlo hDlo hDhi hmm F hF Allowed hAllowed hclass hcut hcutHost hnoshort C₀ hC hehi hlamhi hlamθ a γ ζ ρ Δ hγ hγε heps1 ha hγrate hζ hρ hζ0 hscale τ Asrc BM hBM weight hw BO hBO w hw0 hwupper σE t Jret terr τerr hτerr raw σ ni hni ℓ p k udens pstar BMseed BOseed C Wm Wo W Rsrc R state hub hrow hfixed hcolumn hboundary hrows hpair hboundaryGlobal hstarts hcount hload hbudget hmatching
  have hN':=hN n hn
  have hdec : firstAllLevelSourceAutomaticCoefficientsFin n = firstVortexPrepareCommonTestsFin n := Subsingleton.elim _ _
  have hdec6 : firstAllLevelSourceAutomaticCoefficientsFin 6 = firstVortexPrepareCommonTestsFin 6 := Subsingleton.elim _ _
  try rw [hdec] at hN'
  try rw [hdec6] at hN'
  intro Del δDel hDel hΔ hξDel S T e Q q
  obtain ⟨M,hpos,hdisj,hinc,hlow,hup,hsourceCount⟩:=hmatching Del δDel hDel hΔ
  refine ⟨M,hpos,hdisj,hinc,hlow,hup,hsourceCount,?_⟩
  intro D absorber Reserve X Z habs H A Used P₀ Sel Kbad
  obtain ⟨herr0,herrle⟩:=hbudget Del δDel hDel hΔ
  exact hN' U P π Dv mm β Vort hreg hDv hρhi hρlo hDlo hmm σE Del D t Jret M F hF C₀ a γ δDel hC hehi hlamhi hγ ha hγrate hDel hξDel hrow hinc absorber ζ ρ hζ hρ hζ0 hscale hfixed hcolumn hboundary hrows hpair hboundaryGlobal Allowed hAllowed hK hm hcut hclass hnoshort hcutHost τ Asrc BM hBM weight hw hDhi BO hBO w hw0 hwupper hstarts Reserve X Z p k τerr terr hlamθ hτerr hγε heps1 hload hcount herr0 herrle habs hpos hdisj hlow hup
end Oberwolfach
