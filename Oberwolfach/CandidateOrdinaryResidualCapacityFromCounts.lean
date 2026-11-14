module

public import Oberwolfach.OrdinaryResidualCapacityFromCounts
public import Oberwolfach.OrdinaryCandidateClassReservation
public import Oberwolfach.CandidateOrdinaryAssignedRootCountUpper
public import Oberwolfach.CandidateOrdinaryResidualPrescribedFromCounts
public import Oberwolfach.OrdinaryResidualPrescribedFromCounts
public import Oberwolfach.ResidualMatchingCapacityPolymorphic
public import Oberwolfach.OrdinaryAssignedRootCountUpper
public import Oberwolfach.ResidualActualPrescribedCount
public import Oberwolfach.ActualResidualMissingSum
public import Oberwolfach.OrdinaryUncoveredMarkedSpokeRow
public import Oberwolfach.RawMarkedSpokeExclusive
public import Oberwolfach.RawPackedMissingSpokes

@[expose] public section
/-! Approximate interval positions missed by the selected marked wheels are
bounded by the uncovered hub row of the same physical matching. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U X J:Type} [Fintype U] [DecidableEq U] [Fintype X] [DecidableEq X] [DecidableEq J]

theorem ordinary_residual_capacity_from_matching_and_counts_candidate
    (hn:0<n) (hK:0<K) (m:ℕ) (hm:7≤m)
    (Fam:U→SimpleGraph (Fin n)) (hFam:∀u,(Fam u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (Fam u) Allowed)
    (i₀:Fin K) (rsv θ:ℝ) (hrs0:0≤rsv) (hrs1:rsv≤1/100) (hθ:0<θ) (hθ1:θ≤1/100)
    (hrsclass:rsv≤1/(2*(K:ℝ))) (hclass:∀u,i₀∈factorShortCandidates (Fam u) K)
    (F:SimpleGraph X) (hF:F.IsRegularOfDegree 2) (π:Equiv.Perm (Fin n)) (d:ℕ) (hd:1≤d)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (Rim:(Fin n×Fin n)⊕(Fin n×Fin n)→Prop):
    let H:=rawMarkedPairSpokes π d raw true true
    let RM:=fun W:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>typedMarkedOccurrenceResources W
    let state:=typedMarkedResourceState Rim H
    let RR:=ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W)
    let φ:=ordinaryMixedPhysicalResource (U:=U) π;
    ∀(L:Finset (PhysicalSampledCandidate (mixedCandidateResources RR) state)) (u:U)
    (W:OrdinaryPhysicalMarkedHub (K:=K) π d m RM state L u→
      MarkedWheel (fun e:{e:Fin n×Fin n // Rim (Sum.inl e)}=>e.val.1) (fun e=>e.val.2)
      (fun e:{e:Fin n×Fin n // Rim (Sum.inr e)}=>e.val.1) (fun e=>e.val.2) m π (3*d) (H false) (H true))
    (hW:∀a,(W a).1.val=(ordinaryPhysicalMarkedPayload π d m RM state L u a).1.val ∧ (W a).2.val=u),
    let M:=Finset.univ.image W
    let Q:=physicalSampledCandidateSet φ (mixedCandidateResources RR) state
    let Row:=physicalSampledRow φ state (ordinaryPhysicalRow (.inr (.inr u)))
    let A:=retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret u
    let B:={x:Fin n // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (u,e))) x true};
    ∀a:ActualResidualData (K:=A⊕B) (J:=J) F,
      a.d=d→a.s₁=firstSumIndices→a.s₂=secondSumIndices→
      (∀i:B,a.T (.inr i)=packedPhysicalSpokePositions _ _ _ _ m (3*d) d π (H false) (H true) M u i.val)→
    (∀g,|rawIntervalHubStartCount π d g (fun e=>raw (Sum.inr e)) u-
      (n:ℝ)*ordinaryAssignedMarkedProbability Fam hFam K θ ((m:ℝ)+1) u g/d|<(n:ℝ)^(3/4:ℝ)/d)→
    ∀(κ αCap b z:ℝ) (hαCap:0<αCap) (hb:0≤b),
      (16/(d:ℝ)+16*κ+16*b/αCap+4*z≤θ/8)→
      (32*(n:ℝ)^(3/4:ℝ)/(d:ℝ)+18≤θ*n/8)→
      ((Row\L.biUnion Q).card:ℝ)≤κ*n→
      ∀(G:SimpleGraph (Fin n)) (Z:Finset (Fin n)),
      θ*n/4≤(a.remaining.card:ℝ)→(∀v,(G.degree v:ℝ)≤b*n)→(Z.card:ℝ)≤z*n→
      8*(residualSubtypeSet a.remaining a.prescribed).card+
        8*⌈4*(G.edgeFinset.card:ℝ)/(αCap*Fintype.card (Fin n))⌉₊+4*Z.card+10≤
        Fintype.card {x // x∈a.remaining}:=by
  intro H RM state RR φ L u W hW M Q Row A B a hd' hs₁ hs₂ hpositions hcounts κ αCap b z hαCap hb hbudget hsmall hrow G Z hrem hdegree hZ
  have hp:=ordinary_residual_prescribed_from_matching_and_counts_candidate (K:=K) (J:=J)
    hn hK m hm Fam hFam Allowed hAllowed i₀ rsv θ hrs0 hrs1 hθ hθ1 hrsclass hclass
    F hF π d hd hnoshort raw t Jret Rim L u W hW a hd' hs₁ hs₂ hpositions hcounts κ hrow
  have hcap:=residual_matching_capacity_at_order_polymorphic d (by omega) θ αCap b κ z hθ hαCap hb hbudget n hn hsmall (X:=X)
  exact hcap a.remaining a.prescribed G Z hrem hp hdegree hZ
end Oberwolfach
