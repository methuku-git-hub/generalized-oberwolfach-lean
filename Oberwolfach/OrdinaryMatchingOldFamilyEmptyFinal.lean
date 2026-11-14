module

public import Oberwolfach.OrdinaryMatchingOldFamilySurvivingHost
public import Oberwolfach.ActualFinalEdgesEmpty

@[expose] public section
/-! The same matching's old physical packs are disjoint across the whole
unreserved sources when the final marked indices are empty. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem ordinary_matching_old_family_empty_final_in_surviving_host (π:Equiv.Perm (Fin n)) (d m:ℕ)
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
    ∀(X A B J₁:U→Type) [∀u,Fintype (X u)] [∀u,DecidableEq (X u)]
      [∀u,Fintype (A u)] [∀u,DecidableEq (A u)] [∀u,DecidableEq (B u)] [∀u,DecidableEq (J₁ u)]
      (F:∀u,SimpleGraph (X u)) (data:∀u,ActualResidualData (K:=A u⊕B u) (J:=J₁ u) (F u))
      (ψ:∀u,X u→Fin n),
      (∀u,IsEmpty (A u))→(∀u,(data u).s₁=firstSumIndices)→
      (∀u,ActualOldPhysicalCoverage (data u) (ψ u) (Pack u))→
      (∀u,ActualOldImageDirected (data u) (ψ u) (rawMixedPhysicalArc P π d raw'))→
    let Old:=fun u=>(data u).deletedEdges.image (Sym2.map (ψ u));
    (∀u v,u≠v→Disjoint (Old u) (Old v)) ∧
    ∃All:Finset (Sym2 (Fin n)),(∀u,Old u⊆All) ∧ All⊆(P\Del).edgeFinset  :=by
  intro raw' R H RM state RR φ L hL Pack hPack X A B J₁ _ _ _ _ _ _ F data ψ hempty hs hcover hdir Old
  have hfinal:∀u,(Finset.univ.biUnion (fun i:{i // i∈(data u).s₁}=>((data u).path (.inl i)).edges.toFinset))=∅:=
    fun u=>actual_final_edges_empty_of_empty_first_index (data u) (hempty u) (hs u)
  have hh:=ordinary_matching_old_family_in_surviving_host (K:=K) π d m P Del raw L hL Pack hPack
    X (fun u=>A u⊕B u) J₁ F data ψ hcover hdir
  simpa only [hfinal,Finset.sdiff_empty,Old] using hh
end Oberwolfach
