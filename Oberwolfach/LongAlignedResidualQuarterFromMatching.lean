module

public import Oberwolfach.LongAlignedCycleMassFromSurviving
public import Oberwolfach.LongActualResidualQuarterFromSource

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_aligned_residual_quarter_from_same_matching
    (m d:ℕ) (hm:0<m) (hd:0<d) (θ:ℝ) (hθ:0<θ):
    ∃N:ℕ,∀(n K:ℕ) (hnN:N≤n) (hn:0<n) (U:Type) [Fintype U] [DecidableEq U]
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (π:Equiv.Perm (Fin n)) (ℓ:Fin K→ℕ) (raw:RawMarkedOutcome (Fin n) U Bool Bool)
    (t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (S T:Finset (LongRawHubResource n U)) (hST:S⊆T)
    (M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ))
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
    θ*n/4≤(data.remaining.card:ℝ):=by
  obtain ⟨N,hN⟩:=long_actual_residual_quarter_lower_from_source m d hm hd θ hθ
  refine ⟨N,?_⟩
  intro n K hnN hn U _ _ F hF π ℓ raw t Jret S T hST M e q Nraw w L hmaps assign hhub data hc hd' hs1 hs2 err hθ1 herr hcounts ht hEmbed hlen sourceCard hcount hsource
  letI : DecidableEq L := Classical.decEq _
  have hh:=long_residual_cycle_mass_eq_matching_counts (L:=L) F π d m ℓ e Nraw
  have hh2:=hh hmaps assign hhub w
  have hh3:=hh2 data
  have hh4 : data.Cembed.card=∑i:Fin K,(Nraw.filter (fun c=>c.val.1=some i ∧
      longRawSeedHub π d m ℓ c.val.1 c.val.2=w)).card*ℓ i := by
    apply hh3
    · ext j
      simp only [Finset.mem_univ, iff_true]
      have hj:j∈data.t:=by rw [ht]; exact Finset.mem_univ _
      exact hj
    · exact hEmbed
    · exact hlen
  have hcard:data.Cembed.card=sourceCard:=hh4.trans hcount.symm
  have hmass:|((data.Cembed.card:ℝ)-(n:ℝ)*((1-θ)*(∑i:Fin K,longAssignedKeptFraction F hF K θ i w)))|≤err:=by
    rw [hcard]
    exact hsource
  exact hN hnN hn F hF π (fun e=>raw (Sum.inr e)) t Jret w data hc hd' hs1 hs2 err hθ1 herr hcounts hEmbed data.Cembed.card rfl hmass
end Oberwolfach
