module

public import Oberwolfach.FirstVortexGlobalLoadFromBoundary
public import Oberwolfach.LongInnerTargetsFromAlignedWheels

@[expose] public section
/-! The all-hub forced-image load may use a smaller parameter than the host
embedding budget. Its inputs are the original boundary, row and column tests. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance firstVortexAllHubSmallLoadFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem first_vortex_all_hub_small_load_from_tests
    (δsmall θ:ℝ) (d:ℕ) (hδ:0<δsmall) (hθ:0<θ) (hθδ:10*θ≤δsmall)
    (hspacing:1/(d:ℝ)≤θ/1024):
    ∃N:ℕ,∀(n K m:ℕ),N≤n→0<n→0<K→0<m→1≤d→
    ∀(U:Type) [Fintype U] [DecidableEq U]
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (Del:Finset (Sym2 (Fin n)))
    (t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (A:Finset (Fin n)) (Abs:U→Finset (Fin n)) (ζ ρ a γ:ℝ)
    (hθ1:θ≤1) (hζ:ζ≤θ/4096) (hζ0:0≤ζ) (hρ:ρ≤θ/4096) (hγ:0≤γ)
    (hu:Fintype.card U≤n) (hscale:max a γ*n≤ρ*n)
    (hrows:RetainedRestrictionGood π d (fun e=>raw (Sum.inr e)) false t (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζ Jret)
    (hfixed:∀w,|rawIntervalUnassignedHubCountOn π d (fun e=>raw (Sum.inr e)) w A-
      (A.card:ℝ)*(1-(∑g,longAssignedIntervalProbability F hF K m θ w g)-
        (∑j,longAssignedSpokeProbability F hF K m θ w j))|<(n:ℝ)^(3/4:ℝ))
    (hcolumn:∀v,|rawIntervalUnassignedColumnCount π d (fun e=>raw (Sum.inr e)) v Finset.univ-
      ∑w:U,(1-(∑g,longAssignedIntervalProbability F hF K m θ w g)-
        (∑j,longAssignedSpokeProbability F hF K m θ w j))|<(n:ℝ)^(3/4:ℝ))
    (hboundary:∀v,((rawIntervalBoundaryHubSet π d (fun e=>raw (Sum.inr e)) Finset.univ v).card:ℝ)≤
      4*(Fintype.card U:ℝ)/d+4*(n:ℝ)^(3/4:ℝ)),
    let R:=mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)
    let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
    let S:=longRawSurvivingResources P π d raw true true Del
    let hST:=long_raw_surviving_resources_subset P π d raw true true Del
    let q:=survivingCandidateEmbedding R S T hST
    let Q:=restrictedResourceSet R (Function.Embedding.subtype (·∈S));
    ∀(M:Finset (RestrictedResource R (Function.Embedding.subtype (·∈S)))),
    (∀i,((longRawIncidenceSet S i\M.biUnion Q).card:ℝ)≤max (a*n) (γ*(longRawIncidenceSet S i).card))→
    ∀(assign:LongRawSelectedOrdinary π d m ℓ (Function.Embedding.subtype (·∈T)) (M.map q)↪(Σw,(F w).ConnectedComponent)),
    (∀a,(assign a).1=(longRawSelectedOrdinaryWheel π d m ℓ (Function.Embedding.subtype (·∈T)) (M.map q) a).val.2)→
    ∀(data:∀w,ActualResidualData
      (K:=(retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w) ⊕
        {a:Fin n // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (w,e))) a true})
      (J:={a:LongRawSelectedOrdinary π d m ℓ (Function.Embedding.subtype (·∈T)) (M.map q) // (assign a).1=w}) (F w))
      (ext:∀w,(retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w ⊕
        {a:Fin n // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (w,e))) a true})→Fin ((m+1)*d+5)↪Fin n)
      (paths:∀w,retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w→Fin ((m+1)*d+1)↪Fin n)
      (ψ:∀w,Fin n→Fin n),
    let occupied:=fun w=>((data w).oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) (paths w)).image (ψ w)
    let Z:=innerRequiredTargets Finset.univ A (rawReservedSpokeList π d (fun e=>raw (Sum.inr e)))
      (retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret) Abs occupied;
    (∀w,(data w).c=m+1 ∧ (data w).d=d ∧ (data w).s₂=secondSumIndices ∧
      (∀i,((data w).P i).support=List.ofFn (ext w i)) ∧
      (∀i (j:Fin (d+1)),bufferedMarker (m+1) d (ext w i) j∈(data w).prescribed→
        ψ w (bufferedMarker (m+1) d (ext w i) j)=(π^j.val) (retainedAndRawIntervalRoot π d (fun e=>raw (Sum.inr e)) false true t Jret w i)) ∧
      (∀i,(data w).T i=packedPhysicalSpokePositions _ _ _ _ m (3*d) d π
        (rawMarkedPairSpokes π d raw true true false) (rawMarkedPairSpokes π d raw true true true)
        (longRawMarkedWheelsAtHub P π d m ℓ raw true true (M.map q) w) w
        (retainedAndRawIntervalRoot π d (fun e=>raw (Sum.inr e)) false true t Jret w i)) ∧
      (∀i∈(data w).s₂,∀j:Fin (d+1),∃x∈(data w).oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) (paths w),
        ψ w x=(π^j.val) (retainedAndRawIntervalRoot π d (fun e=>raw (Sum.inr e)) false true t Jret w i)) ∧
      (∀j:{a:LongRawSelectedOrdinary π d m ℓ (Function.Embedding.subtype (·∈T)) (M.map q) // (assign a).1=w},
        ∀v∈Finset.univ.image ((longRawSelectedOrdinaryWheel π d m ℓ (Function.Embedding.subtype (·∈T)) (M.map q) j.val).val.1.val),v∈occupied w) ∧
      (∀W∈longRawMarkedWheelsAtHub P π d m ℓ raw true true (M.map q) w,∀i:Fin (m+1),W.1.val i∈occupied w))→
    ∀(Kbad:SimpleGraph (Fin n)),(∀v,(Kbad.degree v:ℝ)≤δsmall*n/4)→
    ∀v,((Finset.univ.filter (fun w=>v∈(residualSubtypeSet (data w).remaining (data w).prescribed).image (fun x=>ψ w x.1))).card:ℝ)+
      (Kbad.degree v:ℝ)+((Finset.univ.filter (fun w=>v∈Z w)).card:ℝ)≤δsmall*n :=by
  obtain ⟨N,hN⟩:=first_vortex_global_load_from_boundary_tests δsmall θ d hδ hθ hθδ hspacing
  refine ⟨N,?_⟩
  intro n K m hn hn0 hK hm hd U _ _ F hF P π ℓ raw Del t Jret A Abs ζ ρ a γ hθ1 hζ hζ0 hρ hγ hu hscale hrows hfixed hcolumn hboundary R T S hST q Q M hmatch assign hassign data ext paths ψ occupied Z hprops Kbad hKbad
  have hrow0:=long_inner_targets_from_aligned_wheel_images hn0 hK m d hm F hF θ hθ.le hθ1 π
  have heq:instDecidableEqFin n=firstVortexAllHubSmallLoadFin n:=Subsingleton.elim _ _
  have heqK:instDecidableEqFin K=firstVortexAllHubSmallLoadFin K:=Subsingleton.elim _ _
  try rw [heq] at hrow0
  try rw [heqK] at hrow0
  have hrow:=hrow0 raw t Jret Finset.univ A Abs ζ hrows hfixed hcolumn P ℓ Del a γ hγ hu M hmatch assign hassign data paths ψ
    (by intro w;exact ⟨(hprops w).2.2.1,(hprops w).2.2.2.2.2.2.1,(hprops w).2.2.2.2.2.2.2.1,(hprops w).2.2.2.2.2.2.2.2⟩)
  have hN':=hN n K hn U
  have hdec:firstGlobalBoundaryFin n=firstVortexAllHubSmallLoadFin n:=Subsingleton.elim _ _
  have hdecK:firstGlobalBoundaryFin K=firstVortexAllHubSmallLoadFin K:=Subsingleton.elim _ _
  try rw [hdec] at hN'
  try rw [hdecK] at hN'
  have hbound:=hN' P π m (m+1) hd ℓ raw Del t Jret M F data ext ψ
    (fun w=>(hprops w).1) (fun w=>(hprops w).2.1) (fun w=>(hprops w).2.2.1)
    (fun w=>(hprops w).2.2.2.1) (fun w=>(hprops w).2.2.2.2.1) (fun w=>(hprops w).2.2.2.2.2.1)
    a γ hγ hu hmatch hboundary Kbad Z ζ ρ hζ hρ hζ0 hscale hKbad hrow.2
  exact hbound
end Oberwolfach
