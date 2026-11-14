module

public import Oberwolfach.LongSelectedOrientedSourceDynamicCapacity
public import Oberwolfach.LongSelectedOrientedSourceDynamicCapacityUpper
public import Oberwolfach.LongSelectedOrientedSourceWithLoadAndMatching
public import Oberwolfach.LongSelectedOrientedSourceWithMatchingCapacity
public import Oberwolfach.LongSelectedOrientedSourceCapacityUpper
public import Oberwolfach.LongSelectedOrientedSourceGlobalLoad
public import Oberwolfach.LongSelectedOrientedSourceResidualCompletion
public import Oberwolfach.LongSelectedOrientedSourceCapacityUpper
public import Oberwolfach.LongSelectedOrientedSourceGlobalLoad
public import Oberwolfach.LongSelectedOrientedSourceWithMatchingCapacity
public import Oberwolfach.LongSelectedAlignedSourceCapacityUpper
public import Oberwolfach.LongAlignedResidualUpperPrepared

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance firstVortexDynamicResidualUpperFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem first_vortex_dynamic_residual_upper
    (m d:ℕ) (hm:0<m) (hd:m+2≤d) (θ:ℝ) (hθ:0<θ) (hθmax:θ≤1/100)
    (ζret:ℝ) (N:ℕ)
    (hN:∀n:ℕ,N≤n→∀q errOrd:ℝ,
      q≤1/((m:ℝ)+1)→errOrd≤θ*n→
      (n:ℝ)*q/d+(((m+1)*d-1:ℕ):ℝ)*(2*((n:ℝ)^(3/4:ℝ)/d)+ζret*n)+errOrd≤4*θ*n):
    ∀n K:ℕ,N≤n→0<n→3≤K→∀(U:Type) [Fintype U] [DecidableEq U]
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
    (eps lam a γ:ℝ) (heps0:0≤eps) (hγ:0≤γ) (hlam:0≤lam) (hlamθ:lam≤θ)
    (hepsAssign:3*eps≤lam*(θ/(100*(K:ℝ)^2))) (ha:a≤lam/(10*(d:ℝ))) (hγcap:γ≤lam/(10*(d:ℝ)))
    (hdisj:∀c∈M,∀c'∈M,c≠c'→Disjoint (Q c) (Q c'))
    (hmatch:∀i,((longRawIncidenceSet S i\M.biUnion Q).card:ℝ)≤max (a*n) (γ*(longRawIncidenceSet S i).card))
    (hcounts:∀w g,|rawIntervalHubStartCount π d g σ w-
      (n:ℝ)*longAssignedIntervalProbability F hF K m θ w g/(d:ℝ)|<(n:ℝ)^(3/4:ℝ)/(d:ℝ))
    (hgood:RetainedRestrictionGood π d σ false t (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζret Jret)
    (hsourceCount:LongMatchingSourceCountWitness F hF π d m ℓ θ eps T (M.map q))
    (H:Finset U) (A:Finset (Fin n)) (Kbad:Finset (Sym2 (Fin n))→SimpleGraph (Fin n)) (Used:SimpleGraph (Fin n)) (absorber:U→Finset (Fin n)) (δ ρ₀:ℝ)
    (hU:0<Fintype.card U) (Extra:(U→Finset (Fin n))→Finset (Sym2 (Fin n))→Prop),
    LongSelectedOrientedSourceDynamicCapacity hU F P π d m ℓ raw t Jret σE H A Kbad Used absorber δ Extra ρ₀ (M.map q) →
    LongSelectedOrientedSourceDynamicCapacityUpper hU F P π d m ℓ raw t Jret σE H A Kbad Used absorber δ Extra ρ₀ θ (M.map q) :=by
  intro n K hnN hn hK U _ _ P π σE hnoshort Del t Jret ℓ raw σ R T S hST q Q M F hF eps lam a γ heps0 hγ hlam hlamθ hepsAssign ha hγcap hdisj hmatch hcounts hgood hsourceCount H A Kbad Used absorber δ ρ₀ hU Extra hsource
  letI:Nonempty U:=Fintype.card_pos_iff.mp hU
  rcases hsource with ⟨Dsrc,orig,hPair,hValid,hUnion,hArcs,E,hAlign,hLate,ext,inner,ψ,assign,data,hprops,pieces,hpieceEdge,hpieceArc,Pack,hExact,hload,hOldDisj,hOldPack,hApprox,hSelected,hassign,hsize,hUsed,hExtra,hcapacity⟩
  have hUpper0:=long_aligned_residual_upper_from_prepared_matching m d hm hd θ hθ hθmax ζret N hN n K hnN hn hK
  have hdec : alignedResidualUpperPreparedFin n = firstVortexDynamicResidualUpperFin n := Subsingleton.elim _ _
  have hdecK : alignedResidualUpperPreparedFin K = firstVortexDynamicResidualUpperFin K := Subsingleton.elim _ _
  try rw [hdec] at hUpper0
  try rw [hdecK] at hUpper0
  have hUpper:∀w,((data w).remaining.card:ℝ)≤10*θ*n:=by
    intro w
    rcases hprops w with ⟨hc,hd',hs1,hEmbed,_,_,_,_,_,_,_,_,hs2,ht,hT,hlen,_,_,_⟩
    have hpositions:∀x:{x:Fin n // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (w,e))) x true},
      (data w).T (.inr x)=packedPhysicalSpokePositions _ _ _ _ m (3*d) d π
        (rawMarkedPairSpokes π d raw true true false) (rawMarkedPairSpokes π d raw true true true)
        (longRawMarkedWheelsAtHub P π d m ℓ raw true true (M.map q) w) w x.val:=by
      intro x
      simpa only [retainedAndRawIntervalRoot] using hT (.inr x)
    exact hUpper0 U F hF P π raw hnoshort t Jret hgood Del M hdisj w assign hassign hsize (data w) hc hd' hs1 hs2 eps heps0 (hcounts w) ht hEmbed hlen hsourceCount a γ lam hγ hlam hlamθ hepsAssign ha hγcap hmatch hpositions
  refine ⟨Dsrc,orig,hPair,hValid,hUnion,hArcs,E,hAlign,hLate,ext,inner,ψ,assign,data,hprops,pieces,hpieceEdge,hpieceArc,Pack,hExact,hload,hOldDisj,hOldPack,hApprox,hSelected,hassign,hsize,hUsed,hExtra,hcapacity,?_⟩
  exact hUpper
end Oberwolfach
