module

public import Oberwolfach.OrdinaryPhysicalTwoHubRimPacks
public import Oberwolfach.ActualOldPhysicalEdgesDisjoint
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

theorem ordinary_physical_two_hub_buffered_edges_disjoint (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (R:(Fin n×Fin n)⊕(Fin n×Fin n)→Prop) (H:Bool→Fin n→U→Prop):
    let RM:=fun W:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>typedMarkedOccurrenceResources W
    let state:=typedMarkedResourceState R H
    let RR:=ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W)
    let φ:=ordinaryMixedPhysicalResource (U:=U) π;
    ∀(L:Finset (PhysicalSampledCandidate (mixedCandidateResources RR) state))
    (hL:∀x∈L,∀y∈L,x≠y→Disjoint (physicalSampledCandidateSet φ (mixedCandidateResources RR) state x)
      (physicalSampledCandidateSet φ (mixedCandidateResources RR) state y))
    (u v:U) (huv:u≠v)
    (W:OrdinaryPhysicalMarkedHub (K:=K) π d m RM state L u→
      MarkedWheel (fun e:{e:Fin n×Fin n // R (Sum.inl e)}=>e.val.1) (fun e=>e.val.2)
      (fun e:{e:Fin n×Fin n // R (Sum.inr e)}=>e.val.1) (fun e=>e.val.2) m π (3*d) (H false) (H true))
    (Z:OrdinaryPhysicalMarkedHub (K:=K) π d m RM state L v→
      MarkedWheel (fun e:{e:Fin n×Fin n // R (Sum.inl e)}=>e.val.1) (fun e=>e.val.2)
      (fun e:{e:Fin n×Fin n // R (Sum.inr e)}=>e.val.1) (fun e=>e.val.2) m π (3*d) (H false) (H true))
    (hW:∀a,(W a).1.val=(ordinaryPhysicalMarkedPayload π d m RM state L u a).1.val ∧ (W a).2.val=u)
    (hZ:∀a,(Z a).1.val=(ordinaryPhysicalMarkedPayload π d m RM state L v a).1.val ∧ (Z a).2.val=v),
    ∀(X Y K₁ J₁ K₂ J₂:Type) [Fintype X] [Fintype Y] [Fintype K₁] [Fintype J₁] [Fintype K₂] [Fintype J₂]
      [DecidableEq X] [DecidableEq Y] [DecidableEq K₁] [DecidableEq J₁] [DecidableEq K₂] [DecidableEq J₂]
      (F:SimpleGraph X) (G:SimpleGraph Y)
      (data:ActualResidualData (K:=K₁) (J:=J₁) F) (other:ActualResidualData (K:=K₂) (J:=J₂) G)
      (ψ:X→Fin n) (χ:Y→Fin n),
    let P:=mixedWheelRimPack
      (fun a:OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u=>longPaddedSeedExponent (ordinaryPhysicalUnmarkedPayload π d m RM state L u a).1+2)
      (Finset.univ.image W) (fun a=>(ordinaryPhysicalUnmarkedPayload π d m RM state L u a).2)
    let Q:=mixedWheelRimPack
      (fun a:OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L v=>longPaddedSeedExponent (ordinaryPhysicalUnmarkedPayload π d m RM state L v a).1+2)
      (Finset.univ.image Z) (fun a=>(ordinaryPhysicalUnmarkedPayload π d m RM state L v a).2);
    ActualOldPhysicalCoverage data ψ P→ActualOldPhysicalCoverage other χ Q→
      Disjoint (actualOldPhysicalEdges data ψ) (actualOldPhysicalEdges other χ) :=by
  intro RM state RR φ L hL u v huv W Z hW hZ X Y K₁ J₁ K₂ J₂ _ _ _ _ _ _ _ _ _ _ _ _ F G data other ψ χ P Q hP hQ
  have hpacks:=ordinary_physical_two_hub_rim_packs (K:=K) π d m R H L hL u v huv W Z hW hZ
  exact actual_old_physical_edges_disjoint data other ψ χ P Q hP hQ hpacks
end Oberwolfach
