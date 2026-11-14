module

public import Oberwolfach.OrdinaryClassReserveBound
public import Oberwolfach.CandidateOrdinaryUnreservedSizeCapacityMatching
public import Oberwolfach.OrdinaryUnreservedSizeCapacityMatching
public import Oberwolfach.OrdinaryCandidateClassReservation
public import Oberwolfach.CandidateOrdinaryUnreservedCapacityEventuallyDirectReserve
public import Oberwolfach.CandidateOrdinaryUnreservedSizeFromMatchingEventuallyDirectReserve
public import Oberwolfach.OrdinaryUnreservedSizeFromMatchingEventually
public import Oberwolfach.OrdinaryUnreservedCapacityEventually

@[expose] public section
/-! Both the size and matching-capacity bounds use the same retained/raw
starts, physical matching, unreserved source and uncovered spoke row. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance ordinaryResidualSizeCapacityFin_candidate_direct_reserve (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem ordinary_unreserved_size_and_capacity_from_matching_eventually_candidate_direct_reserve
    (m d:ℕ) (hm:7≤m) (hd:1≤d) (θ:ℝ) (hθ:0<θ) (err:ℝ) (herr:0<err):
    ∃N:ℕ,∀{n K:ℕ} (hnN:N≤n) {U:Type} [Fintype U] [DecidableEq U] (hn:0<n) (hK:0<K)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (i₀:Fin K) (rsv:ℝ) (hrs0:0≤rsv) (hrs1:rsv≤1/100)
    (hθ1:θ≤1/100)
    (hClassReserve:OrdinaryClassReserveBound F hF i₀ rsv)
    (π:Equiv.Perm (Fin n)) (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (ζ matchErr κ:ℝ)
    (hgood:RetainedRestrictionGood π d (fun e=>raw (Sum.inr e)) false t
      (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζ Jret)
    (u:U) (Cres:Finset (F u).ConnectedComponent)
    (hsize:∀c:↥Cres,Fintype.card c.val=i₀.val+1)
    (hres:((i₀.val+1:ℕ):ℝ)*Cres.card=rsv*n)
    (hcounts:∀g:Bool,|rawIntervalHubStartCount π d g (fun e=>raw (Sum.inr e)) u-
      (n:ℝ)*ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1) u g/d|<(n:ℝ)^(3/4:ℝ)/d)
    (Rim:(Fin n×Fin n)⊕(Fin n×Fin n)→Prop),
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
      (∑g:Bool,ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1) u g)≤1/8→
      0≤ζ→0≤matchErr→
      1/(8*(d:ℝ))+((m:ℝ)+1)*(d:ℝ)*ζ+matchErr≤err/2→
      ((Row\L.biUnion Q).card:ℝ)≤κ*n→
      ∀δ:ℝ,2*θ+err+((m:ℝ)+2)*κ≤δ→
      ∀errUpper:ℝ,0≤errUpper→errUpper≤θ/8→
      ((∑j:J,(longPaddedSeedExponent (ordinaryPhysicalUnmarkedPayload π d m RM state L u j).1+2)):ℝ)≤
        (1-θ+errUpper)*(n:ℝ)*(∑i:Fin K,ordinaryAssignedKeptFraction F hF K i₀ rsv θ u i)→
      ∀(αCap b z:ℝ),0<αCap→0≤b→
        16/(d:ℝ)+16*κ+16*b/αCap+4*z≤θ/8→
      ∀(G:SimpleGraph (Fin n)) (Z:Finset (Fin n)),
        (∀v,(G.degree v:ℝ)≤b*n)→(Z.card:ℝ)≤z*n→
      (Fintype.card {x // x∈a.remaining}:ℝ)≤δ*n ∧
      8*(residualSubtypeSet a.remaining a.prescribed).card+
        8*⌈4*(G.edgeFinset.card:ℝ)/(αCap*n)⌉₊+4*Z.card+10≤Fintype.card {x // x∈a.remaining}   :=by
  obtain ⟨N₀,hSize⟩:=ordinary_unreserved_residual_size_from_matching_eventually_candidate_direct_reserve m d hd err herr
  obtain ⟨N₁,hCap⟩:=ordinary_unreserved_residual_capacity_eventually_candidate_direct_reserve m d hm hd θ hθ
  refine ⟨max N₀ N₁,?_⟩
  intro n K hnN U _ _ hn hK F hF Allowed hAllowed i₀ rsv hrs0 hrs1 hθ1 hClassReserve π hnoshort raw t Jret ζ matchErr κ hgood u Cres hsize hres hcounts Rim
    H RM state RR φ L W hW M Q Row A B S J a hc hd' hs₁ hs₂ ht hEmbed hlen hpositions hmatch hQ hζ he hrate hrow δ hbudget
    errUpper herrUpper0 herrUpper hmatchUpper αCap b z hα hb hbudgetCap G Z hdegree hZ
  have hsize' := hSize (by omega) hn hK F hF Allowed hAllowed i₀ rsv hrs0 hrs1 hm θ hθ hθ1 hClassReserve π hnoshort raw t Jret ζ matchErr κ hgood u Cres hsize hres hcounts Rim L W hW a hc hd' hs₁ hs₂ ht hEmbed hlen hpositions hmatch hQ hζ he hrate hrow δ hbudget
  have hinst:ordinaryResidualSizeCapacityFin_candidate_direct_reserve n=instDecidableEqFin n:=Subsingleton.elim _ _
  have hcapfn:=hCap (n:=n) (K:=K) (by omega) (U:=U)
  rw [←hinst] at hcapfn
  have hcap:=hcapfn hn hK F hF Allowed hAllowed i₀ rsv hrs0 hrs1 hθ1 hClassReserve π hnoshort raw t Jret Rim L u Cres hsize hres W hW
  have hsum : @instDecidableEqSum A B _ _ = Classical.decEq (A⊕B) := Subsingleton.elim _ _
  dsimp only at hcap
  dsimp only [A,B] at hsum
  rw [←hsum] at hcap
  have hcap':=hcap a hc hd' hs₁ hs₂ hpositions hcounts ht hEmbed hlen errUpper herrUpper0 herrUpper hmatchUpper κ αCap b z hα hb hbudgetCap hrow G Z hdegree hZ
  exact ⟨hsize',by simpa only [Fintype.card_fin] using hcap'⟩
end Oberwolfach
