module

public import Oberwolfach.OrdinaryUnreservedSizeFromMatchingRow
public import Oberwolfach.OrdinaryCandidateClassReservation
public import Oberwolfach.CandidateOrdinaryResidualMatchingMassAndRow
public import Oberwolfach.OrdinaryResidualMatchingMassAndRow

@[expose] public section
/-! The same matching mass and uncovered row directly imply the source-size
hypothesis for simultaneous residual placement. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance ordinaryResidualSizeMatchingFin_candidate (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem ordinary_unreserved_residual_size_from_matching_and_row_candidate
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U] (hn:0<n) (hK:0<K)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (i₀:Fin K) (rsv:ℝ) (hrs0:0≤rsv) (hrs1:rsv≤1/100)
    (m d:ℕ) (hm:7≤m) (hd:1≤d) (θ:ℝ) (hθ:0<θ) (hθ1:θ≤1/100)
    (hrsclass:rsv≤1/(2*(K:ℝ))) (hclass:∀u,i₀∈factorShortCandidates (F u) K)
    (π:Equiv.Perm (Fin n)) (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (ζ matchErr err κ:ℝ)
    (hgood:RetainedRestrictionGood π d (fun e=>raw (Sum.inr e)) false t
      (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζ Jret)
    (u:U) (Cres:Finset (F u).ConnectedComponent)
    (hsize:∀c:↥Cres,Fintype.card c.val=i₀.val+1)
    (hres:((i₀.val+1:ℕ):ℝ)*Cres.card=rsv*n)
    (hcounts:∀g:Bool,|rawIntervalHubStartCount π d g (fun e=>raw (Sum.inr e)) u-
      (n:ℝ)*ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1) u g/d|<(n:ℝ)^(3/4:ℝ)/d)
    (Rim:(Fin n×Fin n)⊕(Fin n×Fin n)→Prop):
    let H:=rawMarkedPairSpokes π d raw true true
    let RM:=fun W:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>typedMarkedOccurrenceResources W
    let state:=typedMarkedResourceState Rim H
    let RR:=ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W)
    let φ:=ordinaryMixedPhysicalResource (U:=U) π;
    ∀(L:Finset (PhysicalSampledCandidate (mixedCandidateResources RR) state))
    (W:OrdinaryPhysicalMarkedHub (K:=K) π d m RM state L u→
      MarkedWheel (fun e:{e:Fin n×Fin n // Rim (Sum.inl e)}=>e.val.1) (fun e=>e.val.2)
      (fun e:{e:Fin n×Fin n // Rim (Sum.inr e)}=>e.val.1) (fun e=>e.val.2) m π (3*d) (H false) (H true))
    (hW:∀a,(W a).1.val=(ordinaryPhysicalMarkedPayload π d m RM state L u a).1.val ∧ (W a).2.val=u),
    let M:=Finset.univ.image W
    let Q:=physicalSampledCandidateSet φ (mixedCandidateResources RR) state
    let Row:=physicalSampledRow φ state (ordinaryPhysicalRow (.inr (.inr u)))
    let A:=retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret u
    let B:={x:Fin n // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (u,e))) x true}
    let S:Set (Fin n):={x | (F u).connectedComponentMk x∉Cres}
    let J:=OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u;
    ∀(a:ActualResidualData (K:=A⊕B) (J:=J) ((F u).induce S)),
      a.c=m+1→a.d=d→a.s₁=firstSumIndices→a.s₂=secondSumIndices→a.t=Finset.univ→
      a.Cembed=a.t.biUnion (fun j=>(a.C j).support.toFinset)→
      (∀j,(a.C j).length=longPaddedSeedExponent (ordinaryPhysicalUnmarkedPayload π d m RM state L u j).1+2)→
      (∀i:B,a.T (.inr i)=packedPhysicalSpokePositions _ _ _ _ m (3*d) d π (H false) (H true) M u i.val)→
      (1-θ-matchErr)*(n:ℝ)*(∑i:Fin K,ordinaryAssignedKeptFraction F hF K i₀ rsv θ u i)≤
        ((∑j:J,(longPaddedSeedExponent (ordinaryPhysicalUnmarkedPayload π d m RM state L u j).1+2)):ℝ)→
      (n:ℝ)*(∑g:Bool,ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1) u g)/d+
        (((m+1)*d-1:ℕ):ℝ)*(2*((n:ℝ)^(3/4:ℝ)/d)+ζ*n)+
        matchErr*n*(∑i:Fin K,ordinaryAssignedKeptFraction F hF K i₀ rsv θ u i)≤err*n→
      ((Row\L.biUnion Q).card:ℝ)≤κ*n→
      ∀δ:ℝ,2*θ+err+((m:ℝ)+2)*κ≤δ→
      (Fintype.card {x // x∈a.remaining}:ℝ)≤δ*n :=by
  intro H RM state RR φ L W hW M Q Row A B S J a hc hd' hs₁ hs₂ ht hEmbed hlen hpositions hmatch herror hrow δ hbudget
  have hh:=ordinary_residual_matching_mass_and_row_candidate hn hK F hF Allowed hAllowed i₀ rsv hrs0 hrs1 m d hm hd θ hθ hθ1 hrsclass hclass
    π hnoshort raw t Jret ζ matchErr err κ hgood u Cres hsize hres hcounts Rim L W hW a hc hd' hs₁ hs₂ ht hEmbed hlen hpositions hmatch herror hrow
  have hh':(a.remaining.card:ℝ)≤(2*θ+err+((m:ℝ)+2)*κ)*n:=by
    simp only [hc,Nat.cast_add,Nat.cast_one] at hh
    nlinarith [hh]
  have hn0:0≤(n:ℝ):=by positivity
  have hb:((2*θ+err+((m:ℝ)+2)*κ)*n)≤δ*n:=mul_le_mul_of_nonneg_right hbudget hn0
  simpa only [Fintype.card_coe] using hh'.trans hb
end Oberwolfach
