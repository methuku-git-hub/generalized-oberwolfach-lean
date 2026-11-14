module

public import Oberwolfach.FirstVortexSourceLoadFromRetainedTests
public import Oberwolfach.LongCapacityAutomaticMargins

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance firstSourceLoadFromHostCutoffFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem first_vortex_source_with_load_from_retained_tests_and_host_cutoff
    (α lam ε δ θ eps ξ:ℝ) (d K m:ℕ)
    (hα:0<α) (hlam:0<lam) (hε:0<ε) (hδ:0<δ) (hθ:0<θ)
    (hθδ:10*θ≤δ) (hθlocal:θ≤δ/32) (hθhi:θ≤1/100)
    (hlamlocal:lam≤δ*ε/32) (hspacing:1/(d:ℝ)≤θ/1024)
    (hd:3≤d) (hK:1≤K) (hm:1≤m)
    (heps:3*eps≤lam*(θ/(100*(K:ℝ)^2))) (hξ:4*ξ≤eps/2):
    ∃N:ℕ,∀n:ℕ,N≤n→∀(U:Type) [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (Dv mm:ℕ) (β:ℝ) (Vort:Vortex U P Dv β ε mm)
    (hreg:P.IsRegularOfDegree Dv) (hDv:0<Dv) (hρhi:initialIndexDensity U Dv≤1)
    (ρ₀:ℝ) (hρ₀:0<ρ₀) (hρlo:ρ₀ ≤ initialIndexDensity U Dv) (hDlo:(n:ℝ)/2≤Dv) (hmm:0<mm)
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
    (hrow:∀v∈A,|(((P.neighborFinset v∩A).filter (fun w=>(σE (Sum.inl s(v,w))).1=4)).card:ℝ)-
      (2*(∑w:U,(1-(1/100:ℝ)-(1/100:ℝ)/(m:ℝ)-longAssignedApproxMarkedWeight F hF K m θ w-longAssignedApproxOrdinaryWeight F hF K m θ w))/(Dv:ℝ))*(P.neighborFinset v∩A).card|<(n:ℝ)^(3/4:ℝ))
    (hmatch:∀i,((longRawIncidenceSet S i\M.biUnion Q).card:ℝ)≤max (a*n) (γ*(longRawIncidenceSet S i).card))
    (hboundary:∀v∈A,((rawIntervalBoundaryHubSet π d σ H v).card:ℝ)≤4*(H.card:ℝ)/d+4*(A.card:ℝ)^(3/4:ℝ))
    (absorber:U→Finset (Fin n))
    (ζ ρ:ℝ) (hζ:ζ≤θ/4096) (hρ:ρ≤θ/4096) (hζ0:0≤ζ)
    (hscale:max a γ*n≤ρ*A.card)
    (hrows:RetainedRestrictionLocalGood π d σ false t A H ζ Jret)
    (hfixed:∀w∈H,|rawIntervalUnassignedHubCountOn π d σ w A-
      (A.card:ℝ)*(1-(∑g,longAssignedIntervalProbability F hF K m θ w g)-
        (∑j,longAssignedSpokeProbability F hF K m θ w j))|<(A.card:ℝ)^(3/4:ℝ))
    (hcolumn:∀v∈A,|rawIntervalUnassignedColumnCount π d σ v H-
      ∑w∈H,(1-(∑g,longAssignedIntervalProbability F hF K m θ w g)-
        (∑j,longAssignedSpokeProbability F hF K m θ w j))|<(A.card:ℝ)^(3/4:ℝ)),
    ∀(Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
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
    (p k τerr terr countErr:ℝ)
    (hlamθ:lam≤θ) (hθ1:θ≤1)
    (hb:∀u,(1/4:ℝ)≤longAssignedApproxOrdinaryWeight F hF K m θ u)
    (hτerr:0≤τerr) (hcount0:0≤countErr) (hcountle:4*countErr≤(eps/2)*n)
    (hγε:γ≤eps) (heps0:0≤eps) (heps1:eps≤1),
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
      longAssignedApproxOrdinaryWeight F hF K m θ u*n|≤countErr)→
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
       LongSelectedAlignedSourceWithLoad hU F P π d m ℓ raw t Jret σE H A Kbad absorber δ (M.map q) :=by
  obtain ⟨N,hN⟩:=first_vortex_source_with_load_from_retained_matching_tests α lam ε δ θ eps ξ d K m hα hlam hε hδ hθ hθδ hθlocal hθhi hlamlocal hspacing hd hK hm heps hξ
  obtain ⟨Nlarge,hlarge⟩:=long_capacity_large_order m θ hθ
  refine ⟨max N Nlarge,?_⟩
  intro n hn U _ _ P π Dv mm β Vort hreg hDv hρhi ρ₀ hρ₀ hρlo hDlo hmm σE DelG D t Jret ℓ raw Del H A σ R T S hST q Q M Used P₀ Sel Kbad F hF C₀ a γ δDel hC hehi hlamhi hγ ha hγrate hDel hδDel hrow hmatch hboundary absorber ζ ρ hζ hρ hζ0 hscale hrows hfixed hcolumn
  intro Allowed hAllowed hK3 hm7 hcut hclass hnoshort hcutHost τ Asrc BM hBM weight hw hDhi BO hBO w hw0 hwupper hstarts Reserve X Z p k τerr terr countErr hlamθ hθ1 hb hτerr hcount0 hcountle hγε heps0 heps1 ni hni selected Hret pstar BMseed BOseed C Wm Wo W Rsrc state hub hload hcount herr0 herrle habs hpos hdisj hlow hup
  exact hN n (le_trans (le_max_left _ _) hn) U P π Dv mm β Vort hreg hDv hρhi ρ₀ hρ₀ hρlo hDlo hmm σE DelG D t Jret M F hF C₀ a γ δDel hC hehi hlamhi hγ ha hγrate hDel hδDel hrow hmatch hboundary absorber ζ ρ hζ hρ hζ0 hscale hrows hfixed hcolumn Allowed hAllowed hK3 hm7 hcut hclass hnoshort (long_capacity_cutoff_succ m d K (by omega) θ hcutHost) (hlarge n (le_trans (le_max_right _ _) hn)) τ Asrc BM hBM weight hw hDhi BO hBO w hw0 hwupper hstarts Reserve X Z p k τerr terr countErr hlamθ hθ1 hb hτerr hcount0 hcountle hγε heps0 heps1 hload hcount herr0 herrle habs hpos hdisj hlow hup
end Oberwolfach
