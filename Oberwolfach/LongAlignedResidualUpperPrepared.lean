module

public import Oberwolfach.LongAlignedResidualCapacityPreparedTargetSum
public import Oberwolfach.LongActualResidualSizeFromSource

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance alignedResidualUpperPreparedFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem long_aligned_residual_upper_from_prepared_matching
    (m d:ℕ) (hm:0<m) (hd:m+2≤d) (θ:ℝ) (hθ:0<θ) (hθmax:θ≤1/100)
    (ζret:ℝ) (N:ℕ)
    (hN:∀n:ℕ,N≤n→∀q errOrd:ℝ,
      q≤1/((m:ℝ)+1)→errOrd≤θ*n→
      (n:ℝ)*q/d+(((m+1)*d-1:ℕ):ℝ)*(2*((n:ℝ)^(3/4:ℝ)/d)+ζret*n)+errOrd≤4*θ*n):
    ∀(n K:ℕ) (hnN:N≤n) (hn:0<n) (hK:3≤K) (U:Type) [Fintype U] [DecidableEq U]
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (raw:RawMarkedOutcome (Fin n) U Bool Bool)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (hgood:RetainedRestrictionGood π d (fun e=>raw (Sum.inr e)) false t
      (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζret Jret)
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
    (eps:ℝ) (heps0:0≤eps)
    (hcounts:∀g,|rawIntervalHubStartCount π d g (fun e=>raw (Sum.inr e)) w-
      (n:ℝ)*longAssignedIntervalProbability F hF K m θ w g/(d:ℝ)|<(n:ℝ)^(3/4:ℝ)/(d:ℝ))
    (ht:data.t=Finset.univ)
    (hEmbed:data.Cembed=data.t.biUnion (fun j=>(data.C j).support.toFinset))
    (hlen:∀j,(data.C j).length=ℓ (longRawSelectedOrdinaryPayload π d m ℓ e Nraw j.val).1)
    (hsource:LongMatchingSourceCountWitness F hF π d m ℓ θ eps T Nraw),
    ∀(a γ lam:ℝ) (hγ:0≤γ) (hlam:0≤lam) (hlamθ:lam≤θ)
    (hepsAssign:3*eps≤lam*(θ/(100*(K:ℝ)^2)))
    (ha:a≤lam/(10*(d:ℝ))) (hγcap:γ≤lam/(10*(d:ℝ)))
    (hmatch:∀i,((longRawIncidenceSet S i\M.biUnion
      (restrictedResourceSet (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) (Function.Embedding.subtype (·∈S)))).card:ℝ)≤
      max (a*n) (γ*(longRawIncidenceSet S i).card))
    (hpositions:∀x:{x:Fin n // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (w,e))) x true},
      data.T (.inr x)=packedPhysicalSpokePositions _ _ _ _ m (3*d) d π
        (rawMarkedPairSpokes π d raw true true false) (rawMarkedPairSpokes π d raw true true true)
        (longRawMarkedWheelsAtHub P π d m ℓ raw true true Nraw w) w x.val),
    (data.remaining.card:ℝ)≤10*θ*n:=by
  intro n K hnN hn hK U _ _ F hF P π raw hnoshort t Jret hgood Del ℓ S T hST M hdisj e q Nraw w L Aidx Bidx assign hhub hsize data hc hd' hs1 hs2 eps heps0 hcounts ht hEmbed hlen hsource a γ lam hγ hlam hlamθ hepsAssign ha hγcap hmatch hpositions
  letI : DecidableEq L := @instDecidableEqSum Aidx Bidx _ _
  have hdec : instDecidableEqFin n = alignedResidualUpperPreparedFin n := Subsingleton.elim _ _
  have hdecK : instDecidableEqFin K = alignedResidualUpperPreparedFin K := Subsingleton.elim _ _
  have hmaps0:=long_aligned_maps_from_surviving_matching_assignment P π d m ℓ raw Del F hF
  try rw [hdec] at hmaps0
  try rw [hdecK] at hmaps0
  have hmaps:=hmaps0 M hdisj assign hhub hsize
  obtain ⟨sourceCard,hcount,herror⟩:=long_matching_source_count_witness_error F hF π d m ℓ θ eps T Nraw hsource w
  have herr:=long_ordinary_mass_error_le_theta_div_100 K n hK θ lam eps hθ.le hθmax hlam hlamθ heps0 hepsAssign
  have herr':((max (3*eps) 0)*(n:ℝ))*(∑i:Fin K,((ℓ i:ℕ):ℝ))≤θ*n:=by
    have hn0:(0:ℝ)≤n:=by positivity
    have hsmall:θ/100*n≤θ*n:=by nlinarith
    exact herr.trans hsmall
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
  have hup0:=long_actual_residual_size_from_source_mass m d hm hd θ hθ hθmax ζret N hN n K hnN hn (by omega) U
  have heq : longActualResidualSizeSourceMassFin n = alignedResidualUpperPreparedFin n := Subsingleton.elim _ _
  have heqK : longActualResidualSizeSourceMassFin K = alignedResidualUpperPreparedFin K := Subsingleton.elim _ _
  try rw [heq] at hup0
  try rw [heqK] at hup0
  exact hup0 F hF P π hnoshort ℓ raw t Jret hgood Del M w lam a γ
    (((max (3*eps) 0)*(n:ℝ))*(∑i:Fin K,((ℓ i:ℕ):ℝ))) hlam hlamθ ha hγ hγcap hmatch herr' hcounts
    (J:={a:LongRawSelectedOrdinary π d m ℓ e Nraw // (assign a).1=w}) data hc hd' hs1 hs2 hpositions hEmbed sourceCard hcard herror
end Oberwolfach
