module

public import Oberwolfach.LongAlignedResidualCapacityOriginalParameters
public import Oberwolfach.FirstVortexResidualTargetSize

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_aligned_residual_capacity_from_local_target_rows
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
    ∀(a γ ρ₀ α lam ε η ζ:ℝ) (hγ:0≤γ) (hρ₀:0<ρ₀) (hα:0<α) (hlam:0≤lam) (hlamθ:lam≤θ)
    (hinv:1/(d:ℝ)≤θ/1024) (ha:a≤lam/(10*(d:ℝ))) (hγcap:γ≤lam/(10*(d:ℝ)))
    (hαsmall:α/16≤((ρ₀/4)/40000)*θ/1024)
    (hρhi:ρ₀≤1) (hεsmall:ε≤(ρ₀/4)/80000) (hη:η≤θ/4096) (hζ:ζ≤θ/4096) (hζ0:0≤ζ)
    (hmatch:∀i,((longRawIncidenceSet S i\M.biUnion
      (restrictedResourceSet (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) (Function.Embedding.subtype (·∈S)))).card:ℝ)≤
      max (a*n) (γ*(longRawIncidenceSet S i).card))
    (G:SimpleGraph (Fin n)) (inner:Finset U) (A:Finset (Fin n))
    (reserved selected absorber occupied:U→Finset (Fin n))
    (hdegree:∀v,(G.degree v:ℝ)≤(α/16)*n)
    (hI:(A.card:ℝ)≤ε*n) (hsub:(A.card:ℝ)^(3/4:ℝ)≤η*n)
    (hrow:∀u∈inner,((innerRequiredTargets inner A reserved selected absorber occupied u).card:ℝ)≤
      2*θ*A.card+(A.card:ℝ)^(3/4:ℝ)+ζ*A.card+max a γ*n)
    (hpositions:∀x:{x:Fin n // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (w,e))) x true},
      data.T (.inr x)=packedPhysicalSpokePositions _ _ _ _ m (3*d) d π
        (rawMarkedPairSpokes π d raw true true false) (rawMarkedPairSpokes π d raw true true true)
        (longRawMarkedWheelsAtHub P π d m ℓ raw true true Nraw w) w x.val),
    8*(residualSubtypeSet data.remaining data.prescribed).card+
      8*⌈4*(G.edgeFinset.card:ℝ)/(((ρ₀/4)/40000)*Fintype.card (Fin n))⌉₊+4*(innerRequiredTargets inner A reserved selected absorber occupied w).card+10≤
      Fintype.card {x // x∈data.remaining}:=by
  obtain ⟨N,hN⟩:=long_aligned_residual_capacity_from_original_parameters m d hm hd θ hθ
  refine ⟨N,?_⟩
  intro n K hnN hn U _ _ F hF P π ℓ raw hnoshort t Jret Del S T hST M e q Nraw w L hmaps assign hhub data hc hd' hs1 hs2 err hθ1 herr hcounts ht hEmbed hlen sourceCard hcount hsource a γ ρ₀ α lam ε η ζ hγ hρ₀ hα hlam hlamθ hinv ha hγcap hαsmall hρhi hεsmall hη hζ hζ0 hmatch G inner A reserved selected absorber occupied hdegree hI hsub hrow hpositions
  letI : DecidableEq L := Classical.decEq _
  have hlam1:lam≤1:=le_trans hlamθ hθ1
  have htarget:=first_vortex_residual_target_size_from_local_rows inner A reserved selected absorber occupied d hd θ ρ₀ ε η ζ lam a γ hθ hρhi hεsmall hI hsub hη hζ hζ0 hlam hlam1 hinv ha hγcap hrow w
  exact hN n K hnN hn U F hF P π ℓ raw hnoshort t Jret Del M w hmaps assign hhub data hc hd' hs1 hs2 err hθ1 herr hcounts ht hEmbed hlen sourceCard hcount hsource a γ ρ₀ α lam (θ/1024) hγ hρ₀ hα hlam hlamθ hinv ha hγcap hαsmall (le_refl _) hmatch G (innerRequiredTargets inner A reserved selected absorber occupied w) hdegree htarget hpositions
end Oberwolfach
