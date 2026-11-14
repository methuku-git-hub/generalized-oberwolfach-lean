module

public import Oberwolfach.FirstVortexActualMatchingLoadFromTests
public import Oberwolfach.LongRequiredFirstVortexDegreeSamplingLaw

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance firstMatchingCompleteLoadFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem first_vortex_complete_matching_local_load_from_common_tests
    (α lam ε δ θ eps ξ:ℝ) (d K m:ℕ)
    (hα:0<α) (hlam:0<lam) (hε:0<ε) (hδ:0<δ) (hθ:0<θ)
    (hθδ:10*θ≤δ) (hθlocal:θ≤δ/32) (hθhi:θ≤1/100)
    (hlamlocal:lam≤δ*ε/32) (hspacing:1/(d:ℝ)≤θ/1024)
    (hd:3≤d) (hK:1≤K) (hm:1≤m)
    (heps:3*eps≤lam*(θ/(100*(K:ℝ)^2))) (hξ:4*ξ≤eps/2):
    ∃N:ℕ,∀n:ℕ,N≤n→∀(U:Type) [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (c:ℕ) (ℓ:Fin K→ℕ)
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
    ∀(F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2) {J:U→Type} [∀w,DecidableEq (J w)]
    (data:∀w,ActualResidualData
      (K:=(retainedMarkedIndex π d σ false t Jret w) ⊕
        {a:Fin n // rawIntervalColouredStart π d (fun e=>σ (w,e)) a true})
      (J:=J w) (F w))
    (ext:∀w,(retainedMarkedIndex π d σ false t Jret w ⊕
      {a:Fin n // rawIntervalColouredStart π d (fun e=>σ (w,e)) a true})→Fin (c*d+5)↪Fin n)
    (ψ:∀w,Fin n→Fin n)
    (hc:∀w,(data w).c=c) (hdd:∀w,(data w).d=d)
    (hs₂:∀w,(data w).s₂=secondSumIndices)
    (hsupp:∀w i,((data w).P i).support=List.ofFn (ext w i))
    (hmarker:∀w i (j:Fin (d+1)),bufferedMarker c d (ext w i) j∈(data w).prescribed→
      ψ w (bufferedMarker c d (ext w i) j)=(π^j.val) (retainedAndRawIntervalRoot π d σ false true t Jret w i))
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
    (absorber occupied:U→Finset (Fin n))
    (ζ ρ:ℝ) (hζ:ζ≤θ/4096) (hρ:ρ≤θ/4096) (hζ0:0≤ζ)
    (hscale:max a γ*n≤ρ*A.card)
    (happrox:∀w x,rawIntervalFamilyState π d σ (x,w)=some (Sum.inl true)→x∈occupied w)
    (hrows:RetainedRestrictionLocalGood π d σ false t A H ζ Jret)
    (hfixed:∀w∈H,|rawIntervalUnassignedHubCountOn π d σ w A-
      (A.card:ℝ)*(1-(∑g,longAssignedIntervalProbability F hF K m θ w g)-
        (∑j,longAssignedSpokeProbability F hF K m θ w j))|<(A.card:ℝ)^(3/4:ℝ))
    (hcolumn:∀v∈A,|rawIntervalUnassignedColumnCount π d σ v H-
      ∑w∈H,(1-(∑g,longAssignedIntervalProbability F hF K m θ w g)-
        (∑j,longAssignedSpokeProbability F hF K m θ w j))|<(A.card:ℝ)^(3/4:ℝ))
    (hOrd:∀(w:U) (x:LongRawSelectedOrdinary π d m ℓ (Function.Embedding.subtype (·∈T)) (M.map q)),
      (longRawSelectedOrdinaryWheel π d m ℓ (Function.Embedding.subtype (·∈T)) (M.map q) x).val.2=w→
      ∀v∈Finset.univ.image ((longRawSelectedOrdinaryWheel π d m ℓ (Function.Embedding.subtype (·∈T)) (M.map q) x).val.1.val),v∈occupied w)
    (hMarked:∀w W,W∈longRawMarkedWheelsAtHub P π d m ℓ raw true true (M.map q) w→
      ∀i:Fin (m+1),W.1.val i∈occupied w),
    let Z:=innerRequiredTargets H A (rawReservedSpokeList π d σ)
      (retainedFinalMarkedAt π d σ t Jret) absorber occupied
    ∀v∈A,((H.filter (fun w=>v∈(residualSubtypeSet (data w).remaining (data w).prescribed).image (fun x=>ψ w x.1))).card:ℝ)+
      Kbad.degree v+((H.filter (fun w=>v∈Z w)).card:ℝ)≤δ*(A.card:ℝ):=by
  have hθhi1:θ≤1:=by linarith only [hθhi]
  have hd1:1≤d:=by omega
  obtain ⟨N₁,hN₁⟩:=first_vortex_actual_matching_local_load_from_event_tests ε δ θ d hε hδ hθ hθδ hθhi1 hspacing
  obtain ⟨N₂,hN₂⟩:=long_required_first_vortex_degree_local_from_sampling_law α lam ε θ δ hα hlam hε hδ hθlocal hlamlocal d K m eps ξ hd hK hm hθ.le hθhi heps hξ
  refine ⟨max N₁ N₂,?_⟩
  intro n hn U _ _ P π c ℓ Dv mm β Vort hreg hDv hρhi hmm σE DelG D t Jret raw Del H A σ R T S hST q Q M Used P₀ Sel Kbad F hF J _ data ext ψ hc hdd hs₂ hsupp hmarker hT C₀ a γ δDel hC hehi hlamhi hγ ha hγrate hDel hδDel hrow hmatch hboundary absorber occupied ζ ρ hζ hρ hζ0 hscale happrox hrows hfixed hcolumn hOrd hMarked Z
  have hn1:N₁≤n:=le_trans (le_max_left _ _) hn
  have hn2:N₂≤n:=le_trans (le_max_right _ _) hn
  have hbad : ∀v∈A,(Kbad.degree v:ℝ)≤δ*(A.card:ℝ)/4:=by
    clear * - hN₂ hn2 hreg hDv hF hρhi hC hehi hlamhi hγ ha hγrate hDel hδDel hrow hmatch hmm
    revert n
    intro n
    have heq : firstMatchingCompleteLoadFin n = instDecidableEqFin n := Subsingleton.elim _ _
    rw [heq]
    letI : DecidableEq (Fin n) := instDecidableEqFin n
    intro P π Vort hreg σE DelG D raw Del A R T S hST q Q M Used P₀ Sel Kbad F hF hDel hδDel hrow hmatch hn2 v hv
    exact hN₂ n hn2 U _ P P₀ Sel DelG Dv mm β Vort hreg hDv F hF hρhi π D (fun x y=>Used.Adj x y) σE true true R M (by
      convert (le_refl P₀) using 1 <;> congr! 6 <;> first | rfl | (congr 1; exact Subsingleton.elim _ _) | exact Subsingleton.elim _ _)
      (by intro x hx y hy hxy; exact hxy) C₀ a γ δDel hC hehi hlamhi hγ ha hγrate hDel hδDel (by
      intro x hx
      convert hrow x hx using 1 <;> congr! 6 <;> first | rfl | (congr 1; exact Subsingleton.elim _ _) | exact Subsingleton.elim _ _) hmatch hmm v
  exact hN₁ n K hn1 hK U P π m c (by omega) hd1 ℓ Dv mm β Vort hreg hDv hρhi hmm raw Del t Jret M F hF data ext ψ hc hdd hs₂ hsupp hmarker hT a γ hγ hmatch hboundary Kbad absorber occupied ζ ρ hζ hρ hζ0 hscale happrox hrows hfixed hcolumn hOrd hMarked hbad
end Oberwolfach
