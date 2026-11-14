module

public import Oberwolfach.FirstVortexActualMatchingLocalLoad
public import Oberwolfach.LongInnerTargetsActualMatchingLocal
public import Oberwolfach.FirstVortexHubCardinality

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance firstActualMatchingTargetAssemblyFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem first_vortex_actual_matching_local_load_from_event_tests
    (ε δ θ:ℝ) (d:ℕ) (hε:0<ε) (hδ:0<δ) (hθ:0<θ)
    (hθδ:10*θ≤δ) (hθhi:θ≤1) (hspacing:1/(d:ℝ)≤θ/1024):
    ∃N:ℕ,∀(n K:ℕ),N≤n→0<K→∀(U:Type) [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (m c:ℕ) (hm:0<m) (hd:1≤d) (ℓ:Fin K→ℕ)
    (Dv mm:ℕ) (β:ℝ) (Vort:Vortex U P Dv β ε mm)
    (hreg:P.IsRegularOfDegree Dv) (hDv:0<Dv) (hρhi:initialIndexDensity U Dv≤1) (hmm:0<mm)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (Del:Finset (Sym2 (Fin n)))
    (t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t),
    let H:=Vort.extendedIndices 1
    let A:=Vort.extendedVertices 1
    let σ:=fun e=>raw (Sum.inr e)
    let R:=mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)
    let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
    let S:=longRawSurvivingResources P π d raw true true Del
    let hST:=long_raw_surviving_resources_subset P π d raw true true Del
    let q:=survivingCandidateEmbedding R S T hST
    let Q:=restrictedResourceSet R (Function.Embedding.subtype (·∈S))
    ∀(M:Finset (RestrictedResource R (Function.Embedding.subtype (·∈S))))
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2) {J:U→Type} [∀w,DecidableEq (J w)]
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
    (a γ:ℝ) (hγ:0≤γ)
    (hmatch:∀i,((longRawIncidenceSet S i\M.biUnion Q).card:ℝ)≤max (a*n) (γ*(longRawIncidenceSet S i).card))
    (hboundary:∀v∈A,((rawIntervalBoundaryHubSet π d σ H v).card:ℝ)≤4*(H.card:ℝ)/d+4*(A.card:ℝ)^(3/4:ℝ))
    (Kbad:SimpleGraph (Fin n)) (absorber occupied:U→Finset (Fin n))
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
    (∀v∈A,(Kbad.degree v:ℝ)≤δ*(A.card:ℝ)/4)→
    ∀v∈A,((H.filter (fun w=>v∈(residualSubtypeSet (data w).remaining (data w).prescribed).image (fun x=>ψ w x.1))).card:ℝ)+
      Kbad.degree v+((H.filter (fun w=>v∈Z w)).card:ℝ)≤δ*(A.card:ℝ):=by
  obtain ⟨N,hN⟩:=first_vortex_actual_matching_local_load_from_target_counts ε δ θ d hε hδ hθ hθδ hspacing
  refine ⟨max N 1,?_⟩
  intro n K hn hK U _ _ P π m c hm hd ℓ Dv mm β Vort hreg hDv hρhi hmm raw Del t Jret H A σ R T S hST q Q M F hF J _ data ext ψ hc hdd hs₂ hsupp hmarker hT a γ hγ hmatch hboundary Kbad absorber occupied ζ ρ hζ hρ hζ0 hscale happrox hrows hfixed hcolumn hOrd hMarked Z hbad
  have hnN:N≤n:=le_trans (le_max_left _ _) hn
  have hn0:0<n:=by omega
  have hu:=first_vortex_hub_cardinality_le_host hreg hn0 hDv hρhi
  have htarget : ∀v∈A,((Finset.univ.filter (fun w=>v∈Z w)).card:ℝ)≤
      2*θ*H.card+(A.card:ℝ)^(3/4:ℝ)+ζ*H.card+max a γ*n :=by
    clear * - hn0 hK hm hF hθhi hθ happrox hrows hfixed hcolumn hreg hDv hρhi hγ hmatch hOrd hMarked
    revert n
    intro n
    have heq : firstActualMatchingTargetAssemblyFin n = instDecidableEqFin n := Subsingleton.elim _ _
    rw [heq]
    letI : DecidableEq (Fin n) := instDecidableEqFin n
    intro P π Vort hreg raw Del Jret H A σ R T S hST q Q M F hF hmatch absorber occupied happrox hrows hfixed hcolumn hOrd hMarked Z hn0
    have hu:=first_vortex_hub_cardinality_le_host hreg hn0 hDv hρhi
    exact (long_inner_targets_from_actual_matching_local hn0 hK m d hm F hF θ hθ.le hθhi π raw t Jret H A absorber occupied happrox ζ hrows hfixed hcolumn P ℓ Del a γ hγ hu M hmatch hOrd hMarked).2
  exact hN n K hnN U P π m c hd ℓ Dv mm β Vort hreg hDv hρhi hmm raw Del t Jret M F data ext ψ hc hdd hs₂ hsupp hmarker hT a γ hγ hmatch hboundary Kbad Z ζ ρ hζ hρ hζ0 hscale hbad htarget
end Oberwolfach
