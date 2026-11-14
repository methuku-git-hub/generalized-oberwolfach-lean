module

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

theorem ordinary_physical_two_hub_rim_packs (π:Equiv.Perm (Fin n)) (d m:ℕ)
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
    Disjoint (mixedWheelRimPack
      (fun a:OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u=>longPaddedSeedExponent (ordinaryPhysicalUnmarkedPayload π d m RM state L u a).1+2)
      (Finset.univ.image W) (fun a=>(ordinaryPhysicalUnmarkedPayload π d m RM state L u a).2))
      (mixedWheelRimPack
      (fun a:OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L v=>longPaddedSeedExponent (ordinaryPhysicalUnmarkedPayload π d m RM state L v a).1+2)
      (Finset.univ.image Z) (fun a=>(ordinaryPhysicalUnmarkedPayload π d m RM state L v a).2)) :=by
  intro RM state RR φ L hL u v huv W Z hW hZ
  apply mixed_wheel_rim_packs_disjoint _ _ (Finset.univ.image W) (Finset.univ.image Z) _ _
  · intro X hX Y hY
    obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hX
    obtain ⟨b,_,rfl⟩:=Finset.mem_image.mp hY
    convert ordinary_physical_restricted_marked_cross_hubs π d m R H L hL u v huv a b (W a) (Z b)
      (hW a).1 ((hW a).2.trans (ordinary_physical_marked_payload_hub π d m RM state L u a).symm)
      (hZ b).1 ((hZ b).2.trans (ordinary_physical_marked_payload_hub π d m RM state L v b).symm) using 1 <;> congr! 5 <;>
      (try (ext z; cases z <;> simp [markedWheelPhysicalResources_rim,markedWheelPhysicalResources_spoke]))
  · intro X hX b
    obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hX
    convert ordinary_physical_restricted_mixed_cross_hubs π d m R H L hL u v a b (W a) (hW a).1
      ((hW a).2.trans (ordinary_physical_marked_payload_hub π d m RM state L u a).symm) using 1 <;> congr! 5 <;>
      (try (ext z; cases z <;> simp [markedWheelPhysicalResources_rim,markedWheelPhysicalResources_spoke]))
  · intro a Y hY
    obtain ⟨b,_,rfl⟩:=Finset.mem_image.mp hY
    convert (ordinary_physical_restricted_mixed_cross_hubs π d m R H L hL v u b a (Z b) (hZ b).1
      ((hZ b).2.trans (ordinary_physical_marked_payload_hub π d m RM state L v b).symm)).symm using 1 <;> congr! 5 <;>
      (try (ext z; cases z <;> simp [markedWheelPhysicalResources_rim,markedWheelPhysicalResources_spoke]))
  · intro a b
    exact ordinary_physical_unmarked_wheels_cross_hubs π d m R H L hL u v huv a b
end Oberwolfach
