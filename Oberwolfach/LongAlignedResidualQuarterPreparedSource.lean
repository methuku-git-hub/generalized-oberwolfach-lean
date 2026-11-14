module

public import Oberwolfach.LongAlignedResidualQuarterFromMatching
public import Oberwolfach.LongAlignedMapsFromMatchingAssignment
public import Oberwolfach.LongMatchingSourceCountError
public import Oberwolfach.LongOrdinaryMassErrorBudgetSharp

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance alignedQuarterSourceWitnessFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem long_aligned_residual_quarter_from_prepared_source_count
    (m d:ℕ) (hm:0<m) (hd:0<d) (θ:ℝ) (hθ:0<θ):
    ∃N:ℕ,∀(n K:ℕ) (hnN:N≤n) (hn:0<n) (hK:3≤K) (U:Type) [Fintype U] [DecidableEq U]
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (raw:RawMarkedOutcome (Fin n) U Bool Bool)
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
    letI : DecidableEq L := Classical.decEq _
    ∀(assign:LongRawSelectedOrdinary π d m ℓ e Nraw↪(Σu,(F u).ConnectedComponent))
    (hhub:∀a,(assign a).1=(longRawSelectedOrdinaryWheel π d m ℓ e Nraw a).val.2)
    (hsize:∀a,Fintype.card (assign a).2=ℓ (longRawSelectedOrdinaryPayload π d m ℓ e Nraw a).1)
    (data:ActualResidualData
      (K:=L)
      (J:={a:LongRawSelectedOrdinary π d m ℓ e Nraw // (assign a).1=w}) (F w))
    (hc:data.c=m+1) (hd':data.d=d)
    (hs1:data.s₁=firstSumIndices) (hs2:data.s₂=secondSumIndices)
    (eps lam:ℝ) (hθmax:θ≤1/100) (heps0:0≤eps) (hlam:0≤lam) (hlamθ:lam≤θ)
    (hepsAssign:3*eps≤lam*(θ/(100*(K:ℝ)^2)))
    (hcounts:∀g,|rawIntervalHubStartCount π d g (fun e=>raw (Sum.inr e)) w-
      (n:ℝ)*longAssignedIntervalProbability F hF K m θ w g/(d:ℝ)|<(n:ℝ)^(3/4:ℝ)/(d:ℝ))
    (ht:data.t=Finset.univ)
    (hEmbed:data.Cembed=data.t.biUnion (fun j=>(data.C j).support.toFinset))
    (hlen:∀j,(data.C j).length=ℓ (longRawSelectedOrdinaryPayload π d m ℓ e Nraw j.val).1)
    (hsource:LongMatchingSourceCountWitness F hF π d m ℓ θ eps T Nraw),
    θ*n/4≤(data.remaining.card:ℝ):=by
  obtain ⟨N,hN⟩:=long_aligned_residual_quarter_from_same_matching m d hm hd θ hθ
  refine ⟨N,?_⟩
  intro n K hnN hn hK U _ _ F hF P π raw t Jret Del ℓ S T hST M hmatch e q Nraw w L assign hhub hsize data hc hd' hs1 hs2 eps lam hθmax heps0 hlam hlamθ hepsAssign hcounts ht hEmbed hlen hsource
  letI : DecidableEq L := Classical.decEq _
  have hmaps0:=long_aligned_maps_from_surviving_matching_assignment P π d m ℓ raw Del F hF
  have hdec : instDecidableEqFin n = alignedQuarterSourceWitnessFin n := Subsingleton.elim _ _
  have hdecK : instDecidableEqFin K = alignedQuarterSourceWitnessFin K := Subsingleton.elim _ _
  try rw [hdec] at hmaps0
  try rw [hdecK] at hmaps0
  have hmaps:=hmaps0 M hmatch assign hhub hsize
  obtain ⟨sourceCard,hcount,herror⟩:=long_matching_source_count_witness_error F hF π d m ℓ θ eps T Nraw hsource w
  have herr:=long_ordinary_mass_error_le_theta_div_100 K n hK θ lam eps hθ.le hθmax hlam hlamθ heps0 hepsAssign
  have hN':=hN n K hnN hn
  try rw [hdec] at hN'
  try rw [hdecK] at hN'
  exact hN' U F hF π ℓ raw t Jret S T hST M w hmaps assign hhub data hc hd' hs1 hs2
    (((max (3*eps) 0)*(n:ℝ))*(∑i:Fin K,((ℓ i:ℕ):ℝ))) (by linarith) herr hcounts ht hEmbed hlen sourceCard hcount herror
end Oberwolfach
