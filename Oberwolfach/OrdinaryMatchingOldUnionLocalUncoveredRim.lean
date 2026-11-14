module

public import Oberwolfach.OrdinaryMatchingRimsInOldUnion
public import Oberwolfach.OrdinaryLocalExceptionalRimDegree
public import Oberwolfach.OrdinaryLocalUncoveredFromCoverage
public import Oberwolfach.OrdinarySampleReferenceActiveContainment

@[expose] public section
/-! The same physical matching, its embedded wheel packs, and the simultaneous
colour counts control the actual sample remainder outside the reference. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_matching_old_union_local_uncovered_rim {n q K:ℕ}
    (Old:Fin q→Finset (Sym2 (Fin n)))
    (P Del:SimpleGraph (Fin n)) (Inner:Finset (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)
    (p k p₂ k₂ u t δ κ:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1) (ht:0≤t)
    (hdegree:∀a:Fin 6,∀x∈Inner,
      |(((P.neighborFinset x∩Inner).filter (fun y=>(σ (Sum.inl s(x,y))).1=a)).card:ℝ)-
        markedExpandedPhysicalProbability p k p₂ k₂ u a*(P.neighborFinset x∩Inner).card|≤t)
    (hDel:∀x,(Del.degree x:ℝ)≤δ):
    let raw:RawMarkedOutcome (Fin n) (Fin q) Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σ e)
    let raw':=rawMarkedDeleteRims raw Del.edgeFinset
    let Host:=ordinaryEligibleHost P π d
    let Rim:=ordinaryShiftedPairRims Host π d raw'
    let H:=rawMarkedPairSpokes π d raw' true true
    let RM:=fun W:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:Fin q)=>True) (fun _ (_:Fin q)=>True)=>typedMarkedOccurrenceResources W
    let state:=typedMarkedResourceState Rim H
    let RR:=ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=Fin q) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W)
    let φ:=ordinaryMixedPhysicalResource (U:=Fin q) π;
    ∀(L:Finset (PhysicalSampledCandidate (mixedCandidateResources RR) state))
    (W:∀v,OrdinaryPhysicalMarkedHub (K:=K) π d m RM state L v→
      MarkedWheel (fun e:{e:Fin n×Fin n // Rim (Sum.inl e)}=>e.val.1) (fun e=>e.val.2)
        (fun e:{e:Fin n×Fin n // Rim (Sum.inr e)}=>e.val.1) (fun e=>e.val.2) m π (3*d) (H false) (H true))
    (hW:∀v a,(W v a).1.val=(ordinaryPhysicalMarkedPayload π d m RM state L v a).1.val ∧ (W v a).2.val=v),
    let Pack:=fun v=>mixedWheelRimPack
      (fun a:OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L v=>longPaddedSeedExponent (ordinaryPhysicalUnmarkedPayload π d m RM state L v a).1+2)
      (Finset.univ.image (W v)) (fun a=>(ordinaryPhysicalUnmarkedPayload π d m RM state L v a).2);
    (∀v edge,edge∈Pack v→∃e∈Old v,e.toFinset=edge)→
    let ι:PhysicalSampledActive φ state↪Sym2 (Fin n)⊕(Fin n×Fin q):=Function.Embedding.subtype _;
    (∀v,(((ordinaryLocalRimIncidence ι v Inner)\L.biUnion (physicalSampledCandidateSet φ (mixedCandidateResources RR) state)).card:ℝ)≤κ)→
    ∀x,((spanningRestriction ((longPhysicalStateGraph P σ {0,1,2,3,4}\longPhysicalStateGraph P σ {0})\
      prescribedPhysicalUnion Old) Inner).degree x:ℝ)≤κ+(2*k+2*k₂+u)*Inner.card+3*t+(6*d+4:ℕ)+δ:=by
  intro raw raw' Host Rim H RM state RR φ L W hW Pack hPack ι hrow x
  let Except:=(((longPhysicalStateGraph P σ {1}⊔longPhysicalStateGraph P σ {3})⊔longPhysicalStateGraph P σ {4})⊔
      (permutationConflictGraph π (3*d+2)⊔Del))
  let loss:ℝ:=(2*k+2*k₂+u)*Inner.card+3*t+(6*d+4:ℕ)+δ
  have hExcept:=ordinary_local_exceptional_rim_degree P Del π d σ Inner p k p₂ k₂ u t δ hp hk hp₂ hk₂ hu hsum ht hdegree hDel
  have hExcept':∀v,((spanningRestriction Except Inner).degree v:ℝ)≤loss:=by
    intro v
    convert hExcept v using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _
  have hactive:=ordinary_sample_reference_active_rim_containment P Del π d σ
  have hpacked:=ordinary_matching_rims_in_old_union (K:=K) Old π d m Rim H L W hW hPack
  have hh:=ordinary_local_uncovered_from_coverage ι Inner L (physicalSampledCandidateSet φ (mixedCandidateResources RR) state) κ loss hrow
    (longPhysicalStateGraph P σ {0,1,2,3,4}) (longPhysicalStateGraph P σ {0})
    (prescribedPhysicalUnion Old) Except hExcept' hactive hpacked x
  convert hh using 1 <;> (try ring) <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
