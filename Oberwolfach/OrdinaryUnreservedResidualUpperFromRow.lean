module

public import Oberwolfach.OrdinaryResidualMissingMatchingRow
public import Oberwolfach.OrdinaryUnreservedMatchingResidualUpper
public import Oberwolfach.OrdinaryPackedMissingMatchingRow
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
variable {n K r:ℕ} {U A J:Type} [Fintype U] [DecidableEq U] [DecidableEq A] [Fintype J] [DecidableEq J]

theorem ordinary_unreserved_residual_upper_from_matching_row
    (F:SimpleGraph (Fin n)) (Cres:Finset F.ConnectedComponent)
    (hsize:∀c:↥Cres,Fintype.card c.val=r) (rsv:ℝ) (hres:(r:ℝ)*Cres.card=rsv*n)
    (π:Equiv.Perm (Fin n)) (d m:ℕ) (hd:1≤d)
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
    let B:={x:Fin n // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (u,e))) x true};
    let S:Set (Fin n):={x | F.connectedComponentMk x∉Cres};
    ∀(a:ActualResidualData (K:=A⊕B) (J:=J) (F.induce S)) (len:J→ℕ),
      a.d=d→a.s₂=secondSumIndices→a.t=Finset.univ→
      a.Cembed=a.t.biUnion (fun j=>(a.C j).support.toFinset)→
      (∀j,(a.C j).length=len j)→
      (∀i:B,a.T (.inr i)=packedPhysicalSpokePositions _ _ _ _ m (3*d) d π (H false) (H true) M u i.val)→
    ∀ε κ:ℝ,
      (1-rsv-ε)*(n:ℝ)≤((∑j,len j):ℝ)+
        ((a.c*a.d-1:ℕ):ℝ)*(a.s₁.card+a.s₂.card)→
      ((Row\L.biUnion Q).card:ℝ)≤κ*n→
      (a.remaining.card:ℝ)≤(ε+(a.c+1)*κ)*n:=by
  intro H RM state RR φ L u W hW M Q Row B S a len hd' hs ht hEmbed hlen hpositions ε κ hmass hrow
  have hm:=ordinary_residual_missing_le_matching_row (K:=K) (A:=A) (J:=J) (F.induce S) π d m hd hnoshort raw t Jret Rim L u W hW a hd' hs hpositions
  have hmR:(((∑i∈a.s₂,(a.d-(a.T i).card)):ℕ):ℝ)≤κ*n:=
    (show (((∑i∈a.s₂,(a.d-(a.T i).card)):ℕ):ℝ)≤((Row\L.biUnion Q).card:ℝ) by exact_mod_cast hm).trans hrow
  exact ordinary_unreserved_matching_residual_upper F Cres hsize rsv hres a len ht hEmbed hlen ε κ hmass hmR
end Oberwolfach
