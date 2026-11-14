module

public import Oberwolfach.OrdinaryUnreservedSizeCapacityMatching

@[expose] public section
/-! The residual size and matching-capacity bounds hold for every hub using
one physical matching and one retained interval sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance ordinaryFamilySizeCapacityFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem ordinary_unreserved_family_size_and_capacity_from_matching_eventually
    (m d:ℕ) (hm:7≤m) (hd:1≤d) (θ:ℝ) (hθ:0<θ) (err:ℝ) (herr:0<err):
    ∃N:ℕ,∀{n K:ℕ} (hnN:N≤n) {U:Type} [Fintype U] [DecidableEq U] (hn:0<n) (hK:0<K)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (i₀:Fin K) (rsv:ℝ) (hrs0:0≤rsv) (hrs1:rsv≤1/100) (hθ1:θ≤1/100)
    (hrsclass:rsv≤1/(2*(K:ℝ))) (hclass:∀u,factorPreparationClass (F u) K=some i₀)
    (π:Equiv.Perm (Fin n)) (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (ζ matchErr κ:ℝ)
    (hgood:RetainedRestrictionGood π d (fun e=>raw (Sum.inr e)) false t
      (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζ Jret)
    (Cres:∀u,Finset (F u).ConnectedComponent)
    (hsize:∀u (c:↥(Cres u)),Fintype.card c.val=i₀.val+1)
    (hres:∀u,((i₀.val+1:ℕ):ℝ)*(Cres u).card=rsv*n)
    (hcounts:∀u (g:Bool),|rawIntervalHubStartCount π d g (fun e=>raw (Sum.inr e)) u-
      (n:ℝ)*ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1) u g/d|<(n:ℝ)^(3/4:ℝ)/d)
    (Rim:(Fin n×Fin n)⊕(Fin n×Fin n)→Prop),
    let H:=rawMarkedPairSpokes π d raw true true
    let RM:=fun W:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>typedMarkedOccurrenceResources W
    let state:=typedMarkedResourceState Rim H
    let RR:=ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W)
    let φ:=ordinaryMixedPhysicalResource (U:=U) π;
    ∀(L:Finset (PhysicalSampledCandidate (mixedCandidateResources RR) state))
    (W:∀u,OrdinaryPhysicalMarkedHub (K:=K) π d m RM state L u→
      MarkedWheel (fun e:{e:Fin n×Fin n // Rim (Sum.inl e)}=>e.val.1) (fun e=>e.val.2)
      (fun e:{e:Fin n×Fin n // Rim (Sum.inr e)}=>e.val.1) (fun e=>e.val.2) m π (3*d) (H false) (H true))
    (hW:∀u a,(W u a).1.val=(ordinaryPhysicalMarkedPayload π d m RM state L u a).1.val ∧ (W u a).2.val=u),
    let Q:=physicalSampledCandidateSet φ (mixedCandidateResources RR) state
    let Row:=fun u=>physicalSampledRow φ state (ordinaryPhysicalRow (.inr (.inr u)))
    let A:=fun u=>retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret u
    let B:=fun u=>{x:Fin n // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (u,e))) x true}
    let S:=fun u=>{x:Fin n | (F u).connectedComponentMk x∉Cres u}
    let J:=fun u=>OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u;
    ∀(a:∀u,ActualResidualData (K:=A u⊕B u) (J:=J u) ((F u).induce (S u))),
      (∀u,(a u).c=m+1)→(∀u,(a u).d=d)→(∀u,(a u).s₁=firstSumIndices)→
      (∀u,(a u).s₂=secondSumIndices)→(∀u,(a u).t=Finset.univ)→
      (∀u,(a u).Cembed=(a u).t.biUnion (fun j=>((a u).C j).support.toFinset))→
      (∀u j,((a u).C j).length=longPaddedSeedExponent (ordinaryPhysicalUnmarkedPayload π d m RM state L u j).1+2)→
      (∀u (i:B u),(a u).T (.inr i)=packedPhysicalSpokePositions _ _ _ _ m (3*d) d π (H false) (H true) (Finset.univ.image (W u)) u i.val)→
      (∀u,(1-θ-matchErr)*(n:ℝ)*(∑i:Fin K,ordinaryAssignedKeptFraction F hF K i₀ rsv θ u i)≤
        ((∑j:J u,(longPaddedSeedExponent (ordinaryPhysicalUnmarkedPayload π d m RM state L u j).1+2)):ℝ))→
      (∀u,(∑g:Bool,ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1) u g)≤1/8)→
      0≤ζ→0≤matchErr→
      1/(8*(d:ℝ))+((m:ℝ)+1)*(d:ℝ)*ζ+matchErr≤err/2→
      (∀u,((Row u\L.biUnion Q).card:ℝ)≤κ*n)→
      ∀δ:ℝ,2*θ+err+((m:ℝ)+2)*κ≤δ→
      ∀errUpper:ℝ,0≤errUpper→errUpper≤θ/8→
      (∀u,((∑j:J u,(longPaddedSeedExponent (ordinaryPhysicalUnmarkedPayload π d m RM state L u j).1+2)):ℝ)≤
        (1-θ+errUpper)*(n:ℝ)*(∑i:Fin K,ordinaryAssignedKeptFraction F hF K i₀ rsv θ u i))→
      ∀(αCap b:ℝ),0<αCap→0≤b→16/(d:ℝ)+16*κ+16*b/αCap≤θ/8→
      ∀(G:SimpleGraph (Fin n)),(∀v,(G.degree v:ℝ)≤b*n)→
      ∀u,(Fintype.card {x // x∈(a u).remaining}:ℝ)≤δ*n ∧
      8*(residualSubtypeSet (a u).remaining (a u).prescribed).card+
        8*⌈4*(G.edgeFinset.card:ℝ)/(αCap*n)⌉₊+10≤Fintype.card {x // x∈(a u).remaining}:=by
  obtain ⟨N,hN⟩:=ordinary_unreserved_size_and_capacity_from_matching_eventually m d hm hd θ hθ err herr
  refine ⟨N,?_⟩
  intro n K hnN U _ _ hn hK F hF Allowed hAllowed i₀ rsv hrs0 hrs1 hθ1 hrsclass hclass π hnoshort raw t Jret ζ matchErr κ hgood Cres hsize hres hcounts Rim
    H RM state RR φ L W hW Q Row A B S J a hc hd' hs₁ hs₂ ht hEmbed hlen hpositions hmatch hQ hζ he hrate hrow δ hbudget errUpper herrUpper0 herrUpper hmatchUpper αCap b hα hb hbudgetCap G hdegree u
  have hh:=hN hnN hn hK F hF Allowed hAllowed i₀ rsv hrs0 hrs1 hθ1 hrsclass hclass π hnoshort raw t Jret ζ matchErr κ hgood u (Cres u) (hsize u) (hres u) (hcounts u) Rim L (W u) (hW u) (a u)
    (hc u) (hd' u) (hs₁ u) (hs₂ u) (ht u) (hEmbed u) (hlen u) (hpositions u) (hmatch u) (hQ u) hζ he hrate (hrow u) δ hbudget errUpper herrUpper0 herrUpper (hmatchUpper u) αCap b 0 hα hb (by simpa using hbudgetCap) G ∅ hdegree (by simp)
  simpa using hh
end Oberwolfach
