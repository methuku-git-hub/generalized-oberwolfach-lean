module

public import Oberwolfach.OrdinaryPhysicalMatchingAllHubPacks
public import Oberwolfach.ActualOldFamilyHostPacking
public import Oberwolfach.RawMixedDeletedArcHost
public import Oberwolfach.OrdinaryEligibleHost
public import Oberwolfach.OrdinaryPhysicalTwoHubRimPacks
public import Oberwolfach.OrdinaryPhysicalRestrictedMarkedFamilyBasic
public import Oberwolfach.OrdinaryPhysicalRestrictedMarkedCrossHubs
public import Oberwolfach.OrdinaryPhysicalRestrictedMixedCrossHubs
public import Oberwolfach.OrdinaryPhysicalUnmarkedWheelsCrossHubs
public import Oberwolfach.MixedWheelRimPacksDisjoint

@[expose] public section
/-! One physical matching supplies rim-edge packs that are pairwise disjoint
across all hubs, with marked and ordinary wheels mixed in each pack. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem ordinary_matching_old_family_in_surviving_host (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (P Del:SimpleGraph (Fin n)) (raw:RawMarkedOutcome (Fin n) U Bool Bool):
    let raw':=rawMarkedDeleteRims raw Del.edgeFinset
    let R:=ordinaryShiftedPairRims P π d raw'
    let H:=rawMarkedPairSpokes π d raw' true true
    let RM:=fun W:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>typedMarkedOccurrenceResources W
    let state:=typedMarkedResourceState R H
    let RR:=ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W)
    let φ:=ordinaryMixedPhysicalResource (U:=U) π;
    ∀(L:Finset (PhysicalSampledCandidate (mixedCandidateResources RR) state))
    (hL:∀x∈L,∀y∈L,x≠y→Disjoint (physicalSampledCandidateSet φ (mixedCandidateResources RR) state x)
      (physicalSampledCandidateSet φ (mixedCandidateResources RR) state y))
    (Pack:U→Finset (Finset (Fin n)))
    (hPack:∀u:U,∃W:OrdinaryPhysicalMarkedHub (K:=K) π d m RM state L u→
      MarkedWheel (fun e:{e:Fin n×Fin n // R (Sum.inl e)}=>e.val.1) (fun e=>e.val.2)
      (fun e:{e:Fin n×Fin n // R (Sum.inr e)}=>e.val.1) (fun e=>e.val.2) m π (3*d) (H false) (H true),
      (∀a,(W a).1.val=(ordinaryPhysicalMarkedPayload π d m RM state L u a).1.val ∧ (W a).2.val=u) ∧
      Pack u=mixedWheelRimPack
        (fun a:OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u=>longPaddedSeedExponent (ordinaryPhysicalUnmarkedPayload π d m RM state L u a).1+2)
        (Finset.univ.image W) (fun a=>(ordinaryPhysicalUnmarkedPayload π d m RM state L u a).2)),
    ∀(X K₁ J₁:U→Type) [∀u,Fintype (X u)] [∀u,DecidableEq (X u)]
      [∀u,DecidableEq (K₁ u)] [∀u,DecidableEq (J₁ u)]
      (F:∀u,SimpleGraph (X u)) (data:∀u,ActualResidualData (K:=K₁ u) (J:=J₁ u) (F u))
      (ψ:∀u,X u→Fin n),
      (∀u,ActualOldPhysicalCoverage (data u) (ψ u) (Pack u))→
      (∀u,ActualOldImageDirected (data u) (ψ u) (rawMixedPhysicalArc P π d raw'))→
    let Old:=fun u=>((data u).deletedEdges\(Finset.univ.biUnion
      (fun i:{i // i∈(data u).s₁}=>((data u).path (.inl i)).edges.toFinset))).image (Sym2.map (ψ u));
    (∀u v,u≠v→Disjoint (Old u) (Old v)) ∧
    ∃All:Finset (Sym2 (Fin n)),(∀u,Old u⊆All) ∧ All⊆(P\Del).edgeFinset :=by
  intro raw' R H RM state RR φ L hL Pack hPack X K₁ J₁ _ _ _ _ F data ψ hcover hdir Old
  letI:DecidableRel (P\Del).Adj:=Classical.decRel _
  have hdis:=ordinary_physical_matching_all_hub_packs_disjoint π d m R H L hL Pack hPack
  have hArc:∀x y,rawMixedPhysicalArc P π d raw' x y→(P\Del).Adj x y:=by
    intro x y h
    exact raw_mixed_deleted_arc_host P Del π d raw x y h
  have hh:=actual_old_family_host_packing F data ψ Pack hcover hdis (P\Del)
    (rawMixedPhysicalArc P π d raw') hArc hdir
  obtain ⟨hpair,All,hAll,hhost⟩:=hh
  refine ⟨hpair,All,hAll,?_⟩
  intro e he
  have he':e∈(P\Del).edgeSet:=
    (@SimpleGraph.mem_edgeFinset (Fin n) (P\Del) e (P\Del).fintypeEdgeSet).mp (hhost he)
  exact (@SimpleGraph.mem_edgeFinset (Fin n) (P\Del) e (P.fintypeEdgeSetSdiff Del)).mpr he'
end Oberwolfach
