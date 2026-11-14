module

public import Oberwolfach.FirstVortexCompleteMatchingLoadFromTests
public import Oberwolfach.LongAlignedSourceOccupancyTests

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance firstMatchingAlignedCompleteLoadFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem first_vortex_aligned_complete_matching_load_from_common_tests
    (α lam ε δ θ eps ξ:ℝ) (d K m:ℕ)
    (hα:0<α) (hlam:0<lam) (hε:0<ε) (hδ:0<δ) (hθ:0<θ)
    (hθδ:10*θ≤δ) (hθlocal:θ≤δ/32) (hθhi:θ≤1/100)
    (hlamlocal:lam≤δ*ε/32) (hspacing:1/(d:ℝ)≤θ/1024)
    (hd:3≤d) (hK:1≤K) (hm:1≤m)
    (heps:3*eps≤lam*(θ/(100*(K:ℝ)^2))) (hξ:4*ξ≤eps/2):
    ∃N:ℕ,∀n:ℕ,N≤n→∀(U:Type) [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (ℓ:Fin K→ℕ)
    (Dv mm:ℕ) (β:ℝ) (Vort:Vortex U P Dv β ε mm)
    (hreg:P.IsRegularOfDegree Dv) (hDv:0<Dv) (hρhi:initialIndexDensity U Dv≤1) (hmm:0<mm)
    (σE:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (DelG:SimpleGraph (Fin n)) (D:Fin n→Fin n→Prop) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (σE (Sum.inr e))) false) t),
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
    (assign:LongRawSelectedOrdinary π d m ℓ (Function.Embedding.subtype (·∈T)) (M.map q)↪(Σw,(F w).ConnectedComponent))
    (hhub:∀x,(assign x).1=(longRawSelectedOrdinaryWheel π d m ℓ (Function.Embedding.subtype (·∈T)) (M.map q) x).val.2)
    (data:∀w,ActualResidualData
      (K:=(retainedMarkedIndex π d σ false t Jret w) ⊕
        {a:Fin n // rawIntervalColouredStart π d (fun e=>σ (w,e)) a true})
      (J:={x:LongRawSelectedOrdinary π d m ℓ (Function.Embedding.subtype (·∈T)) (M.map q) // (assign x).1=w}) (F w))
    (ext:∀w,(retainedMarkedIndex π d σ false t Jret w ⊕
      {a:Fin n // rawIntervalColouredStart π d (fun e=>σ (w,e)) a true})→Fin ((m+1)*d+5)↪Fin n)
    (ψ:∀w,Fin n→Fin n)
    (paths:∀w,retainedMarkedIndex π d σ false t Jret w→Fin ((m+1)*d+1)↪Fin n),
    let occupied:=fun w=>((data w).oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) (paths w)).image (ψ w)
    ∀ (hc:∀w,(data w).c=m+1) (hdd:∀w,(data w).d=d)
    (hs₂:∀w,(data w).s₂=secondSumIndices)
    (hsupp:∀w i,((data w).P i).support=List.ofFn (ext w i))
    (hmarker:∀w i (j:Fin (d+1)),bufferedMarker (m+1) d (ext w i) j∈(data w).prescribed→
      ψ w (bufferedMarker (m+1) d (ext w i) j)=(π^j.val) (retainedAndRawIntervalRoot π d σ false true t Jret w i))
    (hT:∀w i,(data w).T i=packedPhysicalSpokePositions _ _ _ _ m (3*d) d π
      (rawMarkedPairSpokes π d raw true true false) (rawMarkedPairSpokes π d raw true true true)
      (longRawMarkedWheelsAtHub P π d m ℓ raw true true (M.map q) w) w
      (retainedAndRawIntervalRoot π d σ false true t Jret w i))
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
        (∑j,longAssignedSpokeProbability F hF K m θ w j))|<(A.card:ℝ)^(3/4:ℝ))
    (hsource:(∀w,(data w).s₂=secondSumIndices ∧
      (∀i∈(data w).s₂,∀j:Fin (d+1),∃x∈(data w).oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) (paths w),
        ψ w x=(π^j.val) (retainedAndRawIntervalRoot π d σ false true t Jret w i)) ∧
      (∀j:{a:LongRawSelectedOrdinary π d m ℓ (Function.Embedding.subtype (·∈T)) (M.map q) // (assign a).1=w},
        ∀v∈Finset.univ.image ((longRawSelectedOrdinaryWheel π d m ℓ (Function.Embedding.subtype (·∈T)) (M.map q) j.val).val.1.val),v∈occupied w) ∧
      (∀W∈longRawMarkedWheelsAtHub P π d m ℓ raw true true (M.map q) w,∀i:Fin (m+1),W.1.val i∈occupied w))),
    let Z:=innerRequiredTargets H A (rawReservedSpokeList π d σ)
      (retainedFinalMarkedAt π d σ t Jret) absorber occupied
    ∀v∈A,((H.filter (fun w=>v∈(residualSubtypeSet (data w).remaining (data w).prescribed).image (fun x=>ψ w x.1))).card:ℝ)+
      Kbad.degree v+((H.filter (fun w=>v∈Z w)).card:ℝ)≤δ*(A.card:ℝ):=by
  obtain ⟨N,hN⟩:=first_vortex_complete_matching_local_load_from_common_tests α lam ε δ θ eps ξ d K m hα hlam hε hδ hθ hθδ hθlocal hθhi hlamlocal hspacing hd hK hm heps hξ
  refine ⟨max N 1,?_⟩
  intro n hn U _ _ P π ℓ Dv mm β Vort hreg hDv hρhi hmm σE DelG D t Jret raw Del H A σ R T S hST q Q M Used P₀ Sel Kbad F hF assign hhub data ext ψ paths occupied hc hdd hs₂ hsupp hmarker hT C₀ a γ δDel hC hehi hlamhi hγ ha hγrate hDel hδDel hrow hmatch hboundary absorber ζ ρ hζ hρ hζ0 hscale hrows hfixed hcolumn hsource Z
  have hnN:N≤n:=le_trans (le_max_left _ _) hn
  have hOcc : (∀w x,rawIntervalFamilyState π d σ (x,w)=some (Sum.inl true)→x∈occupied w) ∧
    (∀(w:U) (x:LongRawSelectedOrdinary π d m ℓ (Function.Embedding.subtype (·∈T)) (M.map q)),
      (longRawSelectedOrdinaryWheel π d m ℓ (Function.Embedding.subtype (·∈T)) (M.map q) x).val.2=w→
      ∀v∈Finset.univ.image ((longRawSelectedOrdinaryWheel π d m ℓ (Function.Embedding.subtype (·∈T)) (M.map q) x).val.1.val),v∈occupied w) ∧
    (∀w W,W∈longRawMarkedWheelsAtHub P π d m ℓ raw true true (M.map q) w→∀i:Fin (m+1),W.1.val i∈occupied w) :=by
    clear * - hhub hsource
    revert n
    intro n
    have heq : firstMatchingAlignedCompleteLoadFin n = instDecidableEqFin n := Subsingleton.elim _ _
    rw [heq]
    letI : DecidableEq (Fin n) := instDecidableEqFin n
    intro P π σE DelG Jret raw Del σ R T S hST q M F assign hhub data ψ paths occupied hsource
    exact long_aligned_source_occupancy_tests m d F π P ℓ raw Del t Jret M assign hhub data paths ψ hsource
  exact hN n hnN U P π (m+1) ℓ Dv mm β Vort hreg hDv hρhi hmm σE DelG D t Jret M F hF data ext ψ hc hdd hs₂ hsupp hmarker hT C₀ a γ δDel hC hehi hlamhi hγ ha hγrate hDel hδDel hrow hmatch hboundary absorber occupied ζ ρ hζ hρ hζ0 hscale hOcc.1 hrows hfixed hcolumn hOcc.2.1 hOcc.2.2
end Oberwolfach
