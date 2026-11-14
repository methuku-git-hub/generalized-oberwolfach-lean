module

public import Oberwolfach.ActualPrescribedFromBoundarySpokeDefectsDependent
public import Oberwolfach.ActualPrescribedMarkerImageGeometryPolymorphic
public import Oberwolfach.OrdinaryMissingPositionUncoveredSpoke
public import Oberwolfach.OrdinaryUncoveredMarkedSpokeVertexRow
public import Oberwolfach.RawMarkedSpokeExclusive

@[expose] public section
/-! Bound prescribed-image multiplicity by sampled interval boundaries and
uncovered physical matching rows, for dependent unreserved source sets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryPrescribedBoundarySpokeMatchingShape
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    {X J:U→Type} [∀w,Fintype (X w)] [∀w,DecidableEq (X w)] [∀w,DecidableEq (J w)]
    (π:Equiv.Perm (Fin n)) (d m c:ℕ) (hd:1≤d)
    (Rim:(Fin n×Fin n)⊕(Fin n×Fin n)→Prop)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t):Prop :=
    let σ:=fun e=>raw (Sum.inr e)
    let H:=rawMarkedPairSpokes π d raw true true
    let RM:=fun W:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>typedMarkedOccurrenceResources W
    let state:=typedMarkedResourceState Rim H
    let RR:=ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W)
    let φ:=ordinaryMixedPhysicalResource (U:=U) π;
    ∀(L:Finset (PhysicalSampledCandidate (mixedCandidateResources RR) state))
    (W:∀w,OrdinaryPhysicalMarkedHub (K:=K) π d m RM state L w→
      MarkedWheel (fun e:{e:Fin n×Fin n // Rim (Sum.inl e)}=>e.val.1) (fun e=>e.val.2)
        (fun e:{e:Fin n×Fin n // Rim (Sum.inr e)}=>e.val.1) (fun e=>e.val.2) m π (3*d) (H false) (H true))
    (hW:∀w a,(W w a).1.val=(ordinaryPhysicalMarkedPayload π d m RM state L w a).1.val ∧ (W w a).2.val=w)
    (F:∀w,SimpleGraph (X w))
    (data:∀w,ActualResidualData
      (K:=(retainedMarkedIndex π d σ false t Jret w) ⊕
        {a:Fin n // rawIntervalColouredStart π d (fun e=>σ (w,e)) a true}) (J:=J w) (F w))
    (ext:∀w,(retainedMarkedIndex π d σ false t Jret w ⊕
      {a:Fin n // rawIntervalColouredStart π d (fun e=>σ (w,e)) a true})→Fin (c*d+5)↪X w)
    (ψ:∀w,X w→Fin n)
    (hc:∀w,(data w).c=c) (hdd:∀w,(data w).d=d) (hs₂:∀w,(data w).s₂=secondSumIndices)
    (hsupp:∀w i,((data w).P i).support=List.ofFn (ext w i))
    (hmarker:∀w i (j:Fin (d+1)),bufferedMarker c d (ext w i) j∈(data w).prescribed→
      ψ w (bufferedMarker c d (ext w i) j)=(π^j.val) (retainedAndRawIntervalRoot π d σ false true t Jret w i))
    (hT:∀w a,(data w).T (.inr a)=packedPhysicalSpokePositions _ _ _ _ m (3*d) d π (H false) (H true)
      (Finset.univ.image (W w)) w a.val)
    (Bbound Rbound:ℝ),
    let Q:=physicalSampledCandidateSet φ (mixedCandidateResources RR) state
    let Row:=fun v=>physicalSampledRow φ state (ordinaryPhysicalRow (.inr (.inl v)));
    (∀v,((Row v\L.biUnion Q).card:ℝ)≤Rbound)→
    (∀v,((rawIntervalBoundaryHubSet π d σ Finset.univ v).card:ℝ)≤Bbound)→
    ∀v,((Finset.univ.filter (fun w=>v∈(residualSubtypeSet (data w).remaining (data w).prescribed).image (fun x=>ψ w x.1))).card:ℝ)≤
      Bbound+2*Rbound
end Oberwolfach
