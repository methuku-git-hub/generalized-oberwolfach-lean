module

public import Oberwolfach.FirstVortexAllLevelTestsSourceMatching
public import Oberwolfach.LongAssignedMatchingCoefficients

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance firstAllLevelSourceAutomaticCoefficientsFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem first_vortex_all_level_source_matching_with_automatic_coefficients
    (α lam ε δ θ eps ξ ρ₀ bmatch:ℝ) (d K m:ℕ)
    (hα:0<α) (hlam:0<lam) (hε:0<ε) (hδ:0<δ) (hθ:0<θ)
    (hρ₀:0<ρ₀) (hbmatch:0<bmatch) (hαb:α/16≤bmatch)
    (hbd:bmatch≤((ρ₀/4)/40000)/16) (hmarg:4/(m:ℝ)≤bmatch/2) (hεsmall:ε≤(ρ₀/4)/80000)
    (hθδ:10*θ≤δ) (hθlocal:θ≤δ/32) (hθhi:θ≤1/100)
    (hlamlocal:lam≤δ*ε/32) (hspacing:1/(d:ℝ)≤θ/1024)
    (hd:3≤d) (hK:1≤K) (hm:1≤m)
    (heps:3*eps≤lam*(θ/(100*(K:ℝ)^2))) (hξ:4*ξ≤eps/2) (hξ0:0≤ξ):
    ∃N:ℕ,∀n:ℕ,N≤n→∀(U:Type) [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (Dv mm:ℕ) (β:ℝ) (Vort:Vortex U P Dv β ε mm)
    (hreg:P.IsRegularOfDegree Dv) (hDv:0<Dv) (hρhi:initialIndexDensity U Dv≤1)
    (hρlo:ρ₀ ≤ initialIndexDensity U Dv) (hDlo:(n:ℝ)/2≤Dv) (hmm:0<mm)
    (σE:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (DelG:SimpleGraph (Fin n)) (D:Fin n→Fin n→Prop) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (σE (Sum.inr e))) false) t),
    let ℓ:=fun i:Fin K=>longPaddedSeedExponent i+2
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σE e)
    let Del:=DelG.edgeFinset
    let H:=Vort.extendedIndices 1
    let A:=Vort.extendedVertices 1
    let σ:=fun e=>raw (Sum.inr e)
    let R:=mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)
    let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
    let S:=longRawSurvivingResources P π d raw true true Del
    let hST:=long_raw_surviving_resources_subset P π d raw true true Del
    let q:=survivingCandidateEmbedding R S T hST
    let Q:=restrictedResourceSet R (Function.Embedding.subtype (·∈S))
    ∀(M:Finset (RestrictedResource R (Function.Embedding.subtype (·∈S)))),
    let Used:=physicalRimCandidateUnion (markedRawSampledPhysicalEmbedding P π d raw true true)
      (restrictedResourceSet R (Function.Embedding.subtype (·∈T))) (M.map q)
    let P₀:=longPhysicalStateGraph P σE {0,1,2,3,4}\Used
    let Sel:=longSelectedPhysicalGraph P π d σE
    let Kbad:=longRequiredPhysicalGraph P P₀ Sel π d A D (fun x y=>Used.Adj x y)
    ∀(F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (C₀ a γ δDel:ℝ) (hC:1≤C₀) (hehi:ε≤α/(1000*C₀)) (hlamhi:lam≤α/128)
    (hγ:0≤γ) (ha:a≤lam/(10*d)) (hγrate:γ≤lam/(10*d))
    (hDel:∀x,(DelG.degree x:ℝ)≤δDel) (hδDel:δDel≤ξ*n)
    (hrow:∀v,|(((P.neighborFinset v∩A).filter (fun w=>(σE (Sum.inl s(v,w))).1=4)).card:ℝ)-
      (2*(∑w:U,(1-(1/100:ℝ)-(1/100:ℝ)/(m:ℝ)-longAssignedApproxMarkedWeight F hF K m θ w-longAssignedApproxOrdinaryWeight F hF K m θ w))/(Dv:ℝ))*(P.neighborFinset v∩A).card|<(n:ℝ)^(3/4:ℝ))
    (hmatch:∀i,((longRawIncidenceSet S i\M.biUnion Q).card:ℝ)≤max (a*n) (γ*(longRawIncidenceSet S i).card))
    (absorber:U→Finset (Fin n))
    (ζ ρ:ℝ) (hζ:ζ≤θ/4096) (hρ:ρ≤θ/4096) (hζ0:0≤ζ)
    (hscale:max a γ*n≤ρ*A.card)
    (hfixedAll:∀j∈Finset.Icc 1 Vort.length,∀w∈Vort.extendedIndices j,
      |rawIntervalUnassignedHubCountOn π d σ w (Vort.extendedVertices j)-
      ((Vort.extendedVertices j).card:ℝ)*(1-(∑g,longAssignedIntervalProbability F hF K m θ w g)-
        (∑k,longAssignedSpokeProbability F hF K m θ w k))|<((Vort.extendedVertices j).card:ℝ)^(3/4:ℝ))
    (hcolumnAll:∀j∈Finset.Icc 1 Vort.length,∀v∈Vort.extendedVertices j,
      |rawIntervalUnassignedColumnCount π d σ v (Vort.extendedIndices j)-
      ∑w∈Vort.extendedIndices j,(1-(∑g,longAssignedIntervalProbability F hF K m θ w g)-
        (∑k,longAssignedSpokeProbability F hF K m θ w k))|<((Vort.extendedVertices j).card:ℝ)^(3/4:ℝ))
    (hboundaryAll:∀j∈Finset.Icc 1 Vort.length,∀v∈Vort.extendedVertices j,
      ((rawIntervalBoundaryHubSet π d σ (Vort.extendedIndices j) v).card:ℝ)≤
        4*((Vort.extendedIndices j).card:ℝ)/d+4*((Vort.extendedVertices j).card:ℝ)^(3/4:ℝ))
    (hrowsAll:∀j∈Finset.Icc 1 Vort.length,RetainedRestrictionLocalGood π d σ false t
      (Vort.extendedVertices j) (Vort.extendedIndices j) ζ Jret),
    ∀(hpair:∀x y,x≠y→(5/8:ℝ)*(1/100:ℝ)^2*Fintype.card U-(n:ℝ)^(3/4:ℝ)≤
      (((Finset.univ:Finset U).filter (fun w=>rawIntervalFamilyState π d σ (x,w)=some (Sum.inr false) ∧
        rawIntervalFamilyState π d σ (y,w)=some (Sum.inr false))).card:ℝ))
    (hboundaryGlobal:∀v,((rawIntervalExtendedAnyHubSet π d σ v).card:ℝ)≤
      4*(Fintype.card U:ℝ)/(m:ℝ)+4*(n:ℝ)^(3/4:ℝ))
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (hK3:3≤K) (hm7:7≤m)
    (hcut:(1/((m:ℝ)+1))/(d:ℝ)≤θ)
    (hclass:∀u,factorPreparationClass (F u) K=none)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (hcutHost:5/(((m:ℝ)+1)*(d:ℝ)+5)+((m:ℝ)+1)*(d:ℝ)/(K:ℝ)≤θ/2)
    (τ Asrc BM:ℝ) (hBM:0<BM) (weight:(Fin (m+1)→Fin n)→ℝ)
    (hw:SuccessorSequenceWeightConditions P π (3*d) Dv τ Asrc BM weight)
    (hDhi:(Dv:ℝ)≤2*n)
    (BO:Fin K→ℝ) (hBO:∀i,0<BO i)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ) (hw0:∀i C,0≤w i C)
    (hwupper:∀i C,w i C≤BO i/(n:ℝ)^(longPaddedSeedExponent i))
    (hstarts:∀w g,|rawIntervalHubStartCount π d g (fun e=>raw (Sum.inr e)) w-
      (n:ℝ)*longAssignedIntervalProbability F hF K m θ w g/d|<(n:ℝ)^(3/4:ℝ)/d)
    (Reserve:Finset (Finset (Fin n)⊕(Fin n×U))) (X:Finset (Fin n)) (Z:Finset U)
    (p k τerr terr:ℝ)
    (hlamθ:lam≤θ)
    (hτerr:0≤τerr)
    (hγε:γ≤eps) (heps1:eps≤1),
    let ni:=@longPaddedSeedExponent K
    let hni:=@long_padded_seed_exponent_positive K
    let selected:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (σE e)
    let Hret:=retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t Jret false false
    let pstar:=min (1/4:ℝ) (min (ρ₀/8) (ρ₀/(6*((m:ℝ)+1))))
    let BMseed:=2*BM/pstar^(2*m+1)
    let BOseed:=fun i=>2*BO i/pstar^(2*(ni i+2))
    let C:=10*(((m:ℝ)+1)^4*BMseed+∑i:Fin K,((ni i:ℝ)+2)^4*BOseed i)
    let Wm:=longAssignedMarkedSeed F hF K m d θ Dv π weight
    let Wo:=longAssignedOrdinarySeed F hF K m d θ Dv P π ni hni w
    let W:=longMixedSeedWeight Wm Wo
    let Rsrc:=longRawHubResources (U:=U) π d m ℓ
    let state:=longRawHubState P π d raw true true
    let hub:=longRawHubNames (U:=U) π d m ℓ
    (∀(i:Option (Fin K)) (root:LongRawHubResource n U),state root=true→
      |resourcePatternLoad (Rsrc i) (W i) (fun _ _=>true) root state-
        longAssignedMixedTarget F hF K m θ Dv p k i root|≤
        terr+τerr*longAssignedMixedTarget F hF K m θ Dv p k i root)→
    (∀u,|(((ordinaryCommonHubSpokeRoots u).filter (fun v=>state v=true)).card:ℝ)-
      longAssignedApproxOrdinaryWeight F hF K m θ u*n|≤ξ*n)→
    (0≤terr+C*(δDel/(n:ℝ))+4*τerr)→(terr+C*(δDel/(n:ℝ))+4*τerr≤eps/2)→
    MarkedFixedTerminalAbsorber P π d m selected Hret Reserve X Z →
    (∀c∈M,0<mixedCandidateWeight W c.val) →
    (∀c∈M,∀c'∈M,c≠c'→Disjoint (Q c) (Q c')) →
    (∀z:LongRetainedHubTest F hF K θ,
      let test:=longRetainedHubIndicator F hF θ hub z
      let mass:=∑c:RestrictedResource (mixedCandidateResources Rsrc) (Function.Embedding.subtype (·∈S)),test c.val*mixedCandidateWeight W c.val
      (1-γ)*mass≤∑c∈M,test c.val)→
    (∀z:LongRetainedHubTest F hF K θ,
      let test:=longRetainedHubIndicator F hF θ hub z
      let mass:=∑c:RestrictedResource (mixedCandidateResources Rsrc) (Function.Embedding.subtype (·∈S)),test c.val*mixedCandidateWeight W c.val
      (∑c∈M,test c.val)≤(1+γ)*mass)→
    ∃hU:0<Fintype.card U,
       LongSelectedAlignedSourceWithLoadAndMatching hU F P π d m ℓ raw t Jret σE H A Kbad Used absorber δ
        (FirstVortexPrescribedAssignmentOutcome P DelG Used Kbad A π d σE t Jret H α bmatch ρ₀ θ ε lam) (M.map q) :=by
  obtain ⟨N,hN⟩:=first_vortex_source_and_prescribed_matching_from_all_level_tests α lam ε δ θ eps ξ ρ₀ bmatch d K m hα hlam hε hδ hθ hρ₀ hbmatch hαb hbd hmarg hεsmall hθδ hθlocal hθhi hlamlocal hspacing hd hK hm heps hξ hξ0
  refine ⟨max N 1,?_⟩
  intro n hn U _ _ P π Dv mm β Vort hreg hDv hρhi hρlo hDlo hmm σE DelG D t Jret ℓ raw Del H A σ R T S hST q Q M Used P₀ Sel Kbad F hF C₀ a γ δDel hC hehi hlamhi hγ ha hγrate hDel hδDel hrow hmatch absorber ζ ρ hζ hρ hζ0 hscale hfixedAll hcolumnAll hboundaryAll hrowsAll
  intro hpair hboundaryGlobal Allowed hAllowed hK3 hm7 hcut hclass hnoshort hcutHost τ Asrc BM hBM weight hw hDhi BO hBO w hw0 hwupper hstarts Reserve X Z p k τerr terr hlamθ hτerr hγε heps1 ni hni selected Hret pstar BMseed BOseed C Wm Wo W Rsrc state hub hload hcount herr0 herrle habs hpos hdisj hlow hup
  have hn0:0<n:=by omega
  have hDvR:0<(Dv:ℝ):=by exact_mod_cast hDv
  have hsize:initialIndexDensity U Dv*(Dv:ℝ)=2*Fintype.card U:=by
    dsimp [initialIndexDensity]; field_simp
  have hcoeff:=long_assigned_actual_matching_coefficients hn0 F hF Allowed hAllowed K (by omega) m d hm7 (by omega) θ ρ₀ (initialIndexDensity U Dv) Dv (le_of_lt hθ) hθhi hρ₀ hρlo hρhi hDvR hsize hcut hclass
  have hb:∀u,(1/4:ℝ)≤longAssignedApproxOrdinaryWeight F hF K m θ u:=fun u=>(hcoeff.1 u).1
  have hN':=hN n (le_trans (le_max_left _ _) hn)
  have hdec : firstAllLevelTestsSourceMatchingFin n = firstAllLevelSourceAutomaticCoefficientsFin n := Subsingleton.elim _ _
  have hdec6 : firstAllLevelTestsSourceMatchingFin 6 = firstAllLevelSourceAutomaticCoefficientsFin 6 := Subsingleton.elim _ _
  try rw [hdec] at hN'
  try rw [hdec6] at hN'
  exact hN' U P π Dv mm β Vort hreg hDv hρhi hρlo hDlo hmm σE DelG D t Jret M F hF C₀ a γ δDel hC hehi hlamhi hγ ha hγrate hDel hδDel hrow hmatch absorber ζ ρ hζ hρ hζ0 hscale hfixedAll hcolumnAll hboundaryAll hrowsAll hpair hboundaryGlobal Allowed hAllowed hK3 hm7 hcut hclass hnoshort hcutHost τ Asrc BM hBM weight hw hDhi BO hBO w hw0 hwupper hstarts Reserve X Z p k τerr terr hlamθ (by linarith) hb hτerr hγε (le_trans hγ hγε) heps1 hload hcount herr0 herrle habs hpos hdisj hlow hup
end Oberwolfach
