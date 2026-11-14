module

public import Oberwolfach.OrdinaryMatchingOldUnionLocalUncoveredReference
public import Oberwolfach.OrdinaryPostmatchingDemandLocalFromOldUnion
public import Oberwolfach.OrdinaryMatchingOldUnionLocalUncoveredRim
public import Oberwolfach.OrdinaryLocalUncoveredMinusConflict
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

theorem ordinary_actual_local_postmatching_demand {n q K:ℕ}
    (Old:Fin q→Finset (Sym2 (Fin n)))
    (P Del Fbad:SimpleGraph (Fin n)) (Inner:Finset (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)
    (Target Protect:SimpleGraph (Fin n)) (edit:ℝ)
    (p k p₂ k₂ u t δ κ LF:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1) (ht:0≤t)
    (hdegree:∀a:Fin 6,∀x∈Inner,
      |(((P.neighborFinset x∩Inner).filter (fun y=>(σ (Sum.inl s(x,y))).1=a)).card:ℝ)-
        markedExpandedPhysicalProbability p k p₂ k₂ u a*(P.neighborFinset x∩Inner).card|≤t)
    (hDel:∀x,(Del.degree x:ℝ)≤δ) (hF:∀x,(Fbad.degree x:ℝ)≤LF)
    (hOldHost:∀v,Old v⊆P.edgeFinset)
    (hOldRef:∀v,Disjoint (Old v) (longPhysicalStateGraph P σ {0}\Fbad).edgeFinset)
    (hProtect:Protect≤longPhysicalStateGraph P σ {0}\Fbad)
    (hEdit:∀v,((Finset.univ.filter (fun w=>Xor (Target.Adj v w) ((longPhysicalStateGraph P σ {0,1,2,3,4}).Adj v w))).card:ℝ)≤edit):
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
    let Sample:=longPhysicalStateGraph P σ {0,1,2,3,4}
    let Reference:=longPhysicalStateGraph P σ {0}\Fbad
    let Used:=prescribedPhysicalUnion Old
    let G:=ordinaryPostmatchingRequired Target Sample Reference Fbad Used Inner;
    G≤Target\Protect ∧ Disjoint G Used ∧ Disjoint Used Reference ∧
    (∀v,Disjoint (Old v) G.edgeFinset) ∧
    (∀v,(G.degree v:ℝ)≤edit+(κ+(2*k+2*k₂+u)*Inner.card+3*t+(6*d+4:ℕ)+δ+LF)+LF) ∧
    ordinaryForbiddenRequired Target Sample Reference Fbad Inner≤Used⊔G :=by
  intro raw raw' Host Rim H RM state RR φ L W hW Pack hPack ι hrow Sample Reference Used G
  have hRef:Reference≤Sample:=by
    intro x y h
    change (P.Adj x y ∧ (σ (Sum.inl s(x,y))).1∈({0}:Finset (Fin 6))) ∧ ¬Fbad.Adj x y at h
    change P.Adj x y ∧ (σ (Sum.inl s(x,y))).1∈({0,1,2,3,4}:Finset (Fin 6))
    refine ⟨h.1.1,?_⟩
    have hc:(σ (Sum.inl s(x,y))).1=0:=by simpa using h.1.2
    simp [hc]
  have hDis:Disjoint Reference Fbad:=by
    apply disjoint_iff_inf_le.mpr
    intro x y h
    exact (h.1.2 h.2).elim
  let loss:ℝ:=κ+(2*k+2*k₂+u)*Inner.card+3*t+(6*d+4:ℕ)+δ+LF
  have hlocal:∀x,((spanningRestriction ((Sample\Reference)\Used) Inner).degree x:ℝ)≤loss:=by
    intro x
    have hh:=ordinary_matching_old_union_local_uncovered_reference (K:=K) Old P Del Fbad Inner π d m σ
      p k p₂ k₂ u t δ κ LF hp hk hp₂ hk₂ hu hsum ht hdegree hDel hF L W hW hPack hrow x
    convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hh:=ordinary_postmatching_demand_local_from_old_union Old P Target Sample Reference Protect Fbad Inner
    edit loss LF hOldHost (by intro v; convert hOldRef v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    hRef hProtect hDis hEdit hlocal hF
  convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
