module

public import Oberwolfach.LongSelectedProtectedSourceWithMatchingCapacity
public import Oberwolfach.LongSelectedProtectedSourceWithLoadAndMatching
public import Oberwolfach.LongSelectedAlignedSourceWithMatchingCapacity
public import Oberwolfach.LongAlignedResidualCapacityPreparedTargetSum

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance firstVortexProtectedMatchingCapacityFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem first_vortex_protected_source_matching_capacity
    (m d:ℕ) (hm:0<m) (hd:0<d) (θ:ℝ) (hθ:0<θ):
    ∃N:ℕ,∀n K:ℕ,N≤n→0<n→3≤K→∀(U:Type) [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (σE:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (Del:Finset (Sym2 (Fin n))) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d
      (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (σE (Sum.inr e))) false) t),
    let ℓ:=fun i:Fin K=>longPaddedSeedExponent i+2
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σE e)
    let σ:=fun e=>raw (Sum.inr e)
    let R:=mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)
    let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
    let S:=longRawSurvivingResources P π d raw true true Del
    let hST:=long_raw_surviving_resources_subset P π d raw true true Del
    let q:=survivingCandidateEmbedding R S T hST
    let Q:=restrictedResourceSet R (Function.Embedding.subtype (·∈S))
    ∀(M:Finset (RestrictedResource R (Function.Embedding.subtype (·∈S))))
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (eps lam a γ ρ₀ α:ℝ) (hθmax:θ≤1/100) (heps0:0≤eps)
    (hγ:0≤γ) (hρ₀:0<ρ₀) (hα:0<α) (hlam:0≤lam) (hlamθ:lam≤θ)
    (hepsAssign:3*eps≤lam*(θ/(100*(K:ℝ)^2)))
    (hinv:1/(d:ℝ)≤θ/1024) (ha:a≤lam/(10*(d:ℝ))) (hγcap:γ≤lam/(10*(d:ℝ)))
    (hαsmall:α/16≤((ρ₀/4)/40000)*θ/1024)
    (hdisj:∀c∈M,∀c'∈M,c≠c'→Disjoint (Q c) (Q c'))
    (hmatch:∀i,((longRawIncidenceSet S i\M.biUnion Q).card:ℝ)≤max (a*n) (γ*(longRawIncidenceSet S i).card))
    (hcounts:∀w g,|rawIntervalHubStartCount π d g σ w-
      (n:ℝ)*longAssignedIntervalProbability F hF K m θ w g/(d:ℝ)|<(n:ℝ)^(3/4:ℝ)/(d:ℝ))
    (hsourceCount:LongMatchingSourceCountWitness F hF π d m ℓ θ eps T (M.map q))
    (H:Finset U) (A:Finset (Fin n)) (Kbad Used:SimpleGraph (Fin n)) (absorber:U→Finset (Fin n)) (δ:ℝ)
    (hU:0<Fintype.card U)
    (Extra:(U→Finset (Fin n))→Finset (Sym2 (Fin n))→Prop)
    (hExtraDegree:∀occupied Pack,Extra occupied Pack→∀v,(Kbad.degree v:ℝ)≤(α/16)*n)
    (hExtraTarget:∀occupied Pack,Extra occupied Pack→∀w,
      ((innerRequiredTargets H A (rawReservedSpokeList π d σ)
        (retainedFinalMarkedAt π d σ t Jret) absorber occupied w).card:ℝ)≤(θ/1024)*n),
    LongSelectedProtectedSourceWithLoadAndMatching hU F P π d m ℓ raw t Jret σE H A Kbad Used absorber δ Extra (M.map q) →
    LongSelectedProtectedSourceWithLoadMatchingCapacity hU F P π d m ℓ raw t Jret σE H A Kbad Used absorber δ Extra ρ₀ (M.map q) :=by
  obtain ⟨N,hN⟩:=long_aligned_residual_capacity_from_prepared_target_sum m d hm hd θ hθ
  refine ⟨N,?_⟩
  intro n K hnN hn hK U _ _ P π σE hnoshort Del t Jret ℓ raw σ R T S hST q Q M F hF eps lam a γ ρ₀ α hθmax heps0 hγ hρ₀ hα hlam hlamθ hepsAssign hinv ha hγcap hαsmall hdisj hmatch hcounts hsourceCount H A Kbad Used absorber δ hU Extra hExtraDegree hExtraTarget hsource
  letI:Nonempty U:=Fintype.card_pos_iff.mp hU
  rcases hsource with ⟨Dsrc,orig,hPair,hValid,hUnion,hArcs,E,hAlign,hLate,ext,inner,ψ,assign,data,hprops,hload,pieces,hpieceEdge,hpieceArc,Pack,hOldDisj,hOldPack,hApprox,hSelected,hassign,hsize,hUsed,hExtra⟩
  let occupied:=fun w=>((data w).oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w)).image (ψ w)
  let Z:=innerRequiredTargets H A (rawReservedSpokeList π d σ) (retainedFinalMarkedAt π d σ t Jret) absorber occupied
  have hdegree:∀v,(Kbad.degree v:ℝ)≤(α/16)*n:=hExtraDegree occupied Pack hExtra
  have htarget:∀w,((Z w).card:ℝ)≤(θ/1024)*n:=hExtraTarget occupied Pack hExtra
  have hN':=hN n K hnN hn hK
  have hdec : alignedCapacityPreparedTargetSumFin n = firstVortexProtectedMatchingCapacityFin n := Subsingleton.elim _ _
  have hdecK : alignedCapacityPreparedTargetSumFin K = firstVortexProtectedMatchingCapacityFin K := Subsingleton.elim _ _
  try rw [hdec] at hN'
  try rw [hdecK] at hN'
  have hcapacity:∀w,8*(residualSubtypeSet (data w).remaining (data w).prescribed).card+
      8*⌈4*(Kbad.edgeFinset.card:ℝ)/(((ρ₀/4)/40000)*Fintype.card (Fin n))⌉₊+4*(Z w).card+10≤
        Fintype.card {x // x∈(data w).remaining}:=by
    intro w
    have hp:=hprops w
    rcases hp with ⟨hc,hd',hs1,hEmbed,_,_,_,_,_,_,_,_,hs2,ht,hT,hlen,_,_,_⟩
    have hpositions:∀x:{x:Fin n // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (w,e))) x true},
      (data w).T (.inr x)=packedPhysicalSpokePositions _ _ _ _ m (3*d) d π
        (rawMarkedPairSpokes π d raw true true false) (rawMarkedPairSpokes π d raw true true true)
        (longRawMarkedWheelsAtHub P π d m ℓ raw true true (M.map q) w) w x.val:=by
      intro x
      simpa only [retainedAndRawIntervalRoot] using hT (.inr x)
    have hC:=hN' U F hF P π raw hnoshort t Jret Del M hdisj w assign hassign hsize
    exact hC (data w) hc hd' hs1 hs2 eps hθmax heps0 (hcounts w) ht hEmbed hlen hsourceCount a γ ρ₀ α lam hγ hρ₀ hα hlam hlamθ hepsAssign hinv ha hγcap hαsmall hmatch Kbad (Z w) hdegree (htarget w) hpositions
  refine ⟨Dsrc,orig,hPair,hValid,hUnion,hArcs,E,hAlign,hLate,ext,inner,ψ,assign,data,hprops,hload,pieces,hpieceEdge,hpieceArc,Pack,hOldDisj,hOldPack,hApprox,hSelected,hassign,hsize,hUsed,hExtra,?_⟩
  exact hcapacity
end Oberwolfach
