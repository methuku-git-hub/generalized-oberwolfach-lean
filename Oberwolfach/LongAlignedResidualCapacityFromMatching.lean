module

public import Oberwolfach.LongAlignedResidualQuarterFromMatching
public import Oberwolfach.LongResidualCapacityFromCounts

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_aligned_residual_capacity_from_same_matching
    (m d:ℕ) (hm:0<m) (hd:0<d) (θ:ℝ) (hθ:0<θ):
    ∃N:ℕ,∀(n K:ℕ) (hnN:N≤n) (hn:0<n) (U:Type) [Fintype U] [DecidableEq U]
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (ℓ:Fin K→ℕ) (raw:RawMarkedOutcome (Fin n) U Bool Bool)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (Del:Finset (Sym2 (Fin n))),
    let S:=longRawSurvivingResources P π d raw true true Del
    let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
    let hST:=long_raw_surviving_resources_subset P π d raw true true Del
    ∀(M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ))
      (Function.Embedding.subtype (·∈S)))),
    let e:=Function.Embedding.subtype (·∈T)
    let q:=survivingCandidateEmbedding (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) S T hST
    let Nraw:=M.map q
    ∀(w:U),
    let L:=retainedAndRawIntervalIndex π d (fun e=>raw (Sum.inr e)) false true t Jret w
    letI : DecidableEq L := Classical.decEq _
    ∀(hmaps:LongRawOrdinaryComponentMapsProperty F π d m ℓ e Nraw)
    (assign:LongRawSelectedOrdinary π d m ℓ e Nraw↪(Σu,(F u).ConnectedComponent))
    (hhub:∀a,(assign a).1=(longRawSelectedOrdinaryWheel π d m ℓ e Nraw a).val.2)
    (data:ActualResidualData
      (K:=L)
      (J:={a:LongRawSelectedOrdinary π d m ℓ e Nraw // (assign a).1=w}) (F w))
    (hc:data.c=m+1) (hd':data.d=d)
    (hs1:data.s₁=firstSumIndices) (hs2:data.s₂=secondSumIndices)
    (err:ℝ) (hθ1:θ≤1) (herr:err≤(θ/100)*n)
    (hcounts:∀g,|rawIntervalHubStartCount π d g (fun e=>raw (Sum.inr e)) w-
      (n:ℝ)*longAssignedIntervalProbability F hF K m θ w g/(d:ℝ)|<(n:ℝ)^(3/4:ℝ)/(d:ℝ))
    (ht:data.t=Finset.univ)
    (hEmbed:data.Cembed=data.t.biUnion (fun j=>(data.C j).support.toFinset))
    (hlen:∀j,(data.C j).length=ℓ (longRawSelectedOrdinaryPayload π d m ℓ e Nraw j.val).1)
    (sourceCard:ℕ)
    (hcount:sourceCard=∑i:Fin K,(Nraw.filter (fun c=>c.val.1=some i ∧
      longRawSeedHub π d m ℓ c.val.1 c.val.2=w)).card*ℓ i)
    (hsource:|((sourceCard:ℝ)-(n:ℝ)*((1-θ)*(∑i:Fin K,longAssignedKeptFraction F hF K θ i w)))|≤err),
    ∀(a γ αCap b z:ℝ) (hγ:0≤γ) (hαCap:0<αCap) (hb:0≤b)
    (hmatch:∀i,((longRawIncidenceSet S i\M.biUnion
      (restrictedResourceSet (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) (Function.Embedding.subtype (·∈S)))).card:ℝ)≤
      max (a*n) (γ*(longRawIncidenceSet S i).card))
    (hbudget:16/(d:ℝ)+16*max a γ+16*b/αCap+4*z≤θ/8)
    (hsmall:32*(n:ℝ)^(3/4:ℝ)/(d:ℝ)+18≤θ*n/8)
    (G:SimpleGraph (Fin n)) (Z:Finset (Fin n))
    (hdegree:∀v,(G.degree v:ℝ)≤b*n) (hZ:(Z.card:ℝ)≤z*n)
    (hpositions:∀x:{x:Fin n // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (w,e))) x true},
      data.T (.inr x)=packedPhysicalSpokePositions _ _ _ _ m (3*d) d π
        (rawMarkedPairSpokes π d raw true true false) (rawMarkedPairSpokes π d raw true true true)
        (longRawMarkedWheelsAtHub P π d m ℓ raw true true Nraw w) w x.val),
    8*(residualSubtypeSet data.remaining data.prescribed).card+
      8*⌈4*(G.edgeFinset.card:ℝ)/(αCap*Fintype.card (Fin n))⌉₊+4*Z.card+10≤
      Fintype.card {x // x∈data.remaining}:=by
  obtain ⟨N,hN⟩:=long_aligned_residual_quarter_from_same_matching m d hm hd θ hθ
  refine ⟨N,?_⟩
  intro n K hnN hn U _ _ F hF P π ℓ raw hnoshort t Jret Del S T hST M e q Nraw w L hmaps assign hhub data hc hd' hs1 hs2 err hθ1 herr hcounts ht hEmbed hlen sourceCard hcount hsource a γ αCap b z hγ hαCap hb hmatch hbudget hsmall G Z hdegree hZ hpositions
  letI : DecidableEq L := Classical.decEq _
  have hrem:=hN n K hnN hn U F hF π ℓ raw t Jret S T hST M w hmaps assign hhub data hc hd' hs1 hs2 err hθ1 herr hcounts ht hEmbed hlen sourceCard hcount hsource
  have hcap0:=long_actual_residual_matching_capacity_from_common_counts (K:=K) hn P π d m (by omega) hm F hF θ hθ hθ1
  have hdec : longActualResidualCapacityCountsFin n = instDecidableEqFin n := Subsingleton.elim _ _
  have hdecK : longActualResidualCapacityCountsFin K = instDecidableEqFin K := Subsingleton.elim _ _
  try rw [hdec] at hcap0
  try rw [hdecK] at hcap0
  have hcap:=hcap0 hnoshort ℓ raw t Jret Del M w a γ hγ hmatch αCap b z hαCap hb hbudget hsmall
    (J:={a:LongRawSelectedOrdinary π d m ℓ e Nraw // (assign a).1=w})
  let A:=retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w
  let B:={x:Fin n // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (w,e))) x true}
  have hsum : @instDecidableEqSum A B _ _ = Classical.decEq (A⊕B) := Subsingleton.elim _ _
  rw [hsum] at hcap
  exact hcap data G Z hrem hdegree hZ hcounts hs1 hd' hs2 hpositions
end Oberwolfach
