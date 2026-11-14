module

public import Oberwolfach.OrdinaryClassReserveBound
public import Oberwolfach.CandidateOrdinaryUnreservedCapacityEventually
public import Oberwolfach.OrdinaryUnreservedCapacityEventually
public import Oberwolfach.OrdinaryCandidateClassReservation
public import Oberwolfach.CandidateOrdinaryAssignedRootCountUpperDirectReserve
public import Oberwolfach.CandidateOrdinaryUnreservedCapacityFromMatchingDirectReserve
public import Oberwolfach.CandidateOrdinaryUnreservedResidualQuarterFromMatchingDirectReserve
public import Oberwolfach.OrdinaryUnreservedCapacityFromMatching
public import Oberwolfach.LongResidualCapacityAsymptotic
public import Oberwolfach.OrdinaryUnreservedResidualQuarterFromMatching
public import Oberwolfach.OrdinaryUnreservedFactorPaths
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
theorem ordinary_unreserved_residual_capacity_eventually_candidate_direct_reserve
    (m d:ℕ) (hm:7≤m) (hd:1≤d) (θ:ℝ) (hθ:0<θ):
    ∃N:ℕ,∀{n K:ℕ} (hnN:N≤n) {U:Type} [Fintype U] [DecidableEq U]
    (hn:0<n) (hK:0<K)
    (Fam:U→SimpleGraph (Fin n)) (hFam:∀u,(Fam u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (Fam u) Allowed)
    (i₀:Fin K) (rsv:ℝ) (hrs0:0≤rsv) (hrs1:rsv≤1/100) (hθ1:θ≤1/100)
    (hClassReserve:OrdinaryClassReserveBound Fam hFam i₀ rsv)
    (π:Equiv.Perm (Fin n))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (Rim:(Fin n×Fin n)⊕(Fin n×Fin n)→Prop),
    let H:=rawMarkedPairSpokes π d raw true true
    let RM:=fun W:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>typedMarkedOccurrenceResources W
    let state:=typedMarkedResourceState Rim H
    let RR:=ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W)
    let φ:=ordinaryMixedPhysicalResource (U:=U) π;
    ∀(L:Finset (PhysicalSampledCandidate (mixedCandidateResources RR) state)) (u:U)
    (Cres:Finset (Fam u).ConnectedComponent)
    (hsize:∀c:↥Cres,Fintype.card c.val=i₀.val+1)
    (hres:((i₀.val+1:ℕ):ℝ)*Cres.card=rsv*n)
    (W:OrdinaryPhysicalMarkedHub (K:=K) π d m RM state L u→
      MarkedWheel (fun e:{e:Fin n×Fin n // Rim (Sum.inl e)}=>e.val.1) (fun e=>e.val.2)
      (fun e:{e:Fin n×Fin n // Rim (Sum.inr e)}=>e.val.1) (fun e=>e.val.2) m π (3*d) (H false) (H true))
    (hW:∀a,(W a).1.val=(ordinaryPhysicalMarkedPayload π d m RM state L u a).1.val ∧ (W a).2.val=u),
    let M:=Finset.univ.image W
    let Q:=physicalSampledCandidateSet φ (mixedCandidateResources RR) state
    let Row:=physicalSampledRow φ state (ordinaryPhysicalRow (.inr (.inr u)))
    let A:=retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret u
    let B:={x:Fin n // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (u,e))) x true}
    letI : DecidableEq (A⊕B) := Classical.decEq _;
    ∀a:ActualResidualData (K:=A⊕B)
      (J:=OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u)
      ((Fam u).induce {x | (Fam u).connectedComponentMk x∉Cres}),
      a.c=m+1→
      a.d=d→a.s₁=firstSumIndices→a.s₂=secondSumIndices→
      (∀i:B,a.T (.inr i)=packedPhysicalSpokePositions _ _ _ _ m (3*d) d π (H false) (H true) M u i.val)→
    (∀g,|rawIntervalHubStartCount π d g (fun e=>raw (Sum.inr e)) u-
      (n:ℝ)*ordinaryAssignedMarkedProbability Fam hFam K θ ((m:ℝ)+1) u g/d|<(n:ℝ)^(3/4:ℝ)/d)→
    (a.t=Finset.univ)→
    (a.Cembed=a.t.biUnion (fun j=>(a.C j).support.toFinset))→
    (∀j,(a.C j).length=longPaddedSeedExponent (ordinaryPhysicalUnmarkedPayload π d m RM state L u j).1+2)→
    ∀(err:ℝ),0≤err→err≤θ/8→
      ((∑j:OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u,
        (longPaddedSeedExponent (ordinaryPhysicalUnmarkedPayload π d m RM state L u j).1+2)):ℝ)≤
      (1-θ+err)*(n:ℝ)*(∑i:Fin K,ordinaryAssignedKeptFraction Fam hFam K i₀ rsv θ u i)→
    ∀(κ αCap b z:ℝ) (hαCap:0<αCap) (hb:0≤b),
      (16/(d:ℝ)+16*κ+16*b/αCap+4*z≤θ/8)→
      ((Row\L.biUnion Q).card:ℝ)≤κ*n→
      ∀(G:SimpleGraph (Fin n)) (Z:Finset (Fin n)),
      (∀v,(G.degree v:ℝ)≤b*n)→(Z.card:ℝ)≤z*n→
      8*(residualSubtypeSet a.remaining a.prescribed).card+
        8*⌈4*(G.edgeFinset.card:ℝ)/(αCap*Fintype.card (Fin n))⌉₊+4*Z.card+10≤
        Fintype.card {x // x∈a.remaining}:=by
  obtain ⟨N₀,hN₀⟩:=ordinary_unreserved_residual_capacity_from_matching_candidate_direct_reserve m d hm hd θ hθ
  obtain ⟨N₁,hN₁⟩:=long_residual_capacity_sublinear_error θ hθ d (by omega)
  refine ⟨max N₀ N₁,?_⟩
  intro n K hnN U _ _ hn hK Fam hFam Allowed hAllowed i₀ rsv hrs0 hrs1 hθ1 hClassReserve π hnoshort raw t Jret Rim H RM state RR φ L u Cres hsize hres W hW M Q Row A B a hc hd' hs₁ hs₂ hpositions hcounts ht hEmbed hlen err herr0 herr hmatch κ αCap b z hαCap hb hbudget hrow G Z hdegree hZ
  exact hN₀ (by omega) hn hK Fam hFam Allowed hAllowed i₀ rsv hrs0 hrs1 hθ1 hClassReserve π hnoshort raw t Jret Rim
    L u Cres hsize hres W hW a hc hd' hs₁ hs₂ hpositions hcounts ht hEmbed hlen err herr0 herr hmatch
    κ αCap b z hαCap hb hbudget (hN₁ n (by omega)) hrow G Z hdegree hZ
end Oberwolfach
