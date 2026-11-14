module

public import Oberwolfach.LongAlignedResidualCapacityOriginalParameters
public import Oberwolfach.LongAlignedMapsFromMatchingAssignment
public import Oberwolfach.LongMatchingSourceCountError
public import Oberwolfach.LongOrdinaryMassErrorBudgetSharp
public import Oberwolfach.LongActualResidualQuarterLowerSum

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance alignedCapacityPreparedTargetSumFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem long_aligned_residual_capacity_from_prepared_target_sum
    (m d:ℕ) (hm:0<m) (hd:0<d) (θ:ℝ) (hθ:0<θ):
    ∃N:ℕ,∀(n K:ℕ) (hnN:N≤n) (hn:0<n) (hK:3≤K) (U:Type) [Fintype U] [DecidableEq U]
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (raw:RawMarkedOutcome (Fin n) U Bool Bool)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (Del:Finset (Sym2 (Fin n))),
    let ℓ:=fun i:Fin K=>longPaddedSeedExponent i+2
    let S:=longRawSurvivingResources P π d raw true true Del
    let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
    let hST:=long_raw_surviving_resources_subset P π d raw true true Del
    ∀(M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ))
      (Function.Embedding.subtype (·∈S)))),
    (∀c∈M,∀c'∈M,c≠c'→Disjoint
      (restrictedResourceSet (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) (Function.Embedding.subtype (·∈S)) c)
      (restrictedResourceSet (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) (Function.Embedding.subtype (·∈S)) c'))→
    let e:=Function.Embedding.subtype (·∈T)
    let q:=survivingCandidateEmbedding (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) S T hST
    let Nraw:=M.map q
    ∀(w:U),
    let L:=retainedAndRawIntervalIndex π d (fun e=>raw (Sum.inr e)) false true t Jret w
    let Aidx:=retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w
    let Bidx:={x:Fin n // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (w,e))) x true}
    letI : DecidableEq L := @instDecidableEqSum Aidx Bidx _ _
    ∀(assign:LongRawSelectedOrdinary π d m ℓ e Nraw↪(Σu,(F u).ConnectedComponent))
    (hhub:∀a,(assign a).1=(longRawSelectedOrdinaryWheel π d m ℓ e Nraw a).val.2)
    (hsize:∀a,Fintype.card (assign a).2=ℓ (longRawSelectedOrdinaryPayload π d m ℓ e Nraw a).1)
    (data:ActualResidualData
      (K:=L)
      (J:={a:LongRawSelectedOrdinary π d m ℓ e Nraw // (assign a).1=w}) (F w))
    (hc:data.c=m+1) (hd':data.d=d)
    (hs1:data.s₁=firstSumIndices) (hs2:data.s₂=secondSumIndices)
    (eps:ℝ) (hθmax:θ≤1/100) (heps0:0≤eps)
    (hcounts:∀g,|rawIntervalHubStartCount π d g (fun e=>raw (Sum.inr e)) w-
      (n:ℝ)*longAssignedIntervalProbability F hF K m θ w g/(d:ℝ)|<(n:ℝ)^(3/4:ℝ)/(d:ℝ))
    (ht:data.t=Finset.univ)
    (hEmbed:data.Cembed=data.t.biUnion (fun j=>(data.C j).support.toFinset))
    (hlen:∀j,(data.C j).length=ℓ (longRawSelectedOrdinaryPayload π d m ℓ e Nraw j.val).1)
    (hsource:LongMatchingSourceCountWitness F hF π d m ℓ θ eps T Nraw),
    ∀(a γ ρ₀ α lam:ℝ) (hγ:0≤γ) (hρ₀:0<ρ₀) (hα:0<α) (hlam:0≤lam) (hlamθ:lam≤θ)
    (hepsAssign:3*eps≤lam*(θ/(100*(K:ℝ)^2)))
    (hinv:1/(d:ℝ)≤θ/1024) (ha:a≤lam/(10*(d:ℝ))) (hγcap:γ≤lam/(10*(d:ℝ)))
    (hαsmall:α/16≤((ρ₀/4)/40000)*θ/1024)
    (hmatch:∀i,((longRawIncidenceSet S i\M.biUnion
      (restrictedResourceSet (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) (Function.Embedding.subtype (·∈S)))).card:ℝ)≤
      max (a*n) (γ*(longRawIncidenceSet S i).card))
    (G:SimpleGraph (Fin n)) (Z:Finset (Fin n))
    (hdegree:∀v,(G.degree v:ℝ)≤(α/16)*n) (hZ:(Z.card:ℝ)≤(θ/1024)*n)
    (hpositions:∀x:{x:Fin n // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (w,e))) x true},
      data.T (.inr x)=packedPhysicalSpokePositions _ _ _ _ m (3*d) d π
        (rawMarkedPairSpokes π d raw true true false) (rawMarkedPairSpokes π d raw true true true)
        (longRawMarkedWheelsAtHub P π d m ℓ raw true true Nraw w) w x.val),
    8*(residualSubtypeSet data.remaining data.prescribed).card+
      8*⌈4*(G.edgeFinset.card:ℝ)/(((ρ₀/4)/40000)*Fintype.card (Fin n))⌉₊+4*Z.card+10≤
      Fintype.card {x // x∈data.remaining}:=by
  obtain ⟨N,hQuarter⟩:=long_actual_residual_quarter_lower_from_counts_sum m d hm hd θ hθ
  obtain ⟨Nsmall,hNsmall⟩:=long_residual_capacity_sublinear_error θ hθ d hd
  refine ⟨max N Nsmall,?_⟩
  intro n K hnN hn hK U _ _ F hF P π raw hnoshort t Jret Del ℓ S T hST M hdisj e q Nraw w L Aidx Bidx assign hhub hsize data hc hd' hs1 hs2 eps hθmax heps0 hcounts ht hEmbed hlen hsource a γ ρ₀ α lam hγ hρ₀ hα hlam hlamθ hepsAssign hinv ha hγcap hαsmall hmatch G Z hdegree hZ hpositions
  letI : DecidableEq L := @instDecidableEqSum Aidx Bidx _ _
  have hdec : instDecidableEqFin n = alignedCapacityPreparedTargetSumFin n := Subsingleton.elim _ _
  have hdecK : instDecidableEqFin K = alignedCapacityPreparedTargetSumFin K := Subsingleton.elim _ _
  have hmaps0:=long_aligned_maps_from_surviving_matching_assignment P π d m ℓ raw Del F hF
  try rw [hdec] at hmaps0
  try rw [hdecK] at hmaps0
  have hmaps:=hmaps0 M hdisj assign hhub hsize
  obtain ⟨sourceCard,hcount,herror⟩:=long_matching_source_count_witness_error F hF π d m ℓ θ eps T Nraw hsource w
  have herr:=long_ordinary_mass_error_le_theta_div_100 K n hK θ lam eps hθ.le hθmax hlam hlamθ heps0 hepsAssign
  have hh:=long_residual_cycle_mass_eq_matching_counts (L:=L) F π d m ℓ e Nraw
  try rw [hdec] at hh
  try rw [hdecK] at hh
  have hh2:=hh hmaps assign hhub w
  have hh3:=hh2 data
  have hcard:data.Cembed.card=sourceCard:=by
    apply Eq.trans ?_ hcount.symm
    apply hh3
    · ext j
      simp only [Finset.mem_univ, iff_true]
      have hj:j∈data.t:=by rw [ht]; exact Finset.mem_univ _
      exact hj
    · exact hEmbed
    · exact hlen
  have hQuarter':=hQuarter (n:=n) (K:=K) (U:=U) (J:={a:LongRawSelectedOrdinary π d m ℓ e Nraw // (assign a).1=w}) (le_trans (le_max_left _ _) hnN)
  try rw [hdec] at hQuarter'
  try rw [hdecK] at hQuarter'
  have hC:=residual_ordinary_mass_upper_from_source_count data hEmbed sourceCard hcard
    ((n:ℝ)*((1-θ)*(∑i:Fin K,longAssignedKeptFraction F hF K θ i w)))
    (((max (3*eps) 0)*(n:ℝ))*(∑i:Fin K,((ℓ i:ℕ):ℝ))) herror
  have hrem:=hQuarter' hn F hF π (fun e=>raw (Sum.inr e)) t Jret w data hc hd' hs1 hs2
    (((max (3*eps) 0)*(n:ℝ))*(∑i:Fin K,((ℓ i:ℕ):ℝ))) (by linarith) herr hcounts hC
  have hcap0:=long_actual_residual_matching_capacity_from_common_counts (K:=K) hn P π d m (by omega) hm F hF θ hθ (by linarith : θ≤1)
  have hcapdec : longActualResidualCapacityCountsFin n = alignedCapacityPreparedTargetSumFin n := Subsingleton.elim _ _
  have hcapdecK : longActualResidualCapacityCountsFin K = alignedCapacityPreparedTargetSumFin K := Subsingleton.elim _ _
  try rw [hcapdec] at hcap0
  try rw [hcapdecK] at hcap0
  have hcap:0<((ρ₀/4)/40000):=by positivity
  have hbudget:=first_vortex_residual_matching_budget d hd θ ρ₀ α lam a γ (θ/1024) hθ (by linarith) hρ₀ hlam hlamθ hinv ha hγcap hαsmall (le_refl _)
  exact hcap0 hnoshort ℓ raw t Jret Del M w a γ hγ hmatch ((ρ₀/4)/40000) (α/16) (θ/1024) hcap (by positivity) hbudget
    (hNsmall n (le_trans (le_max_right _ _) hnN)) (J:={a:LongRawSelectedOrdinary π d m ℓ e Nraw // (assign a).1=w}) data G Z hrem hdegree hZ hcounts hs1 hd' hs2 hpositions
end Oberwolfach
