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
set_option synthInstance.maxSize 65536
set_option maxRecDepth 8192
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
def ordinaryPhysicalPairHubRimPacksShape {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U] (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (R:(Fin n×Fin n)⊕(Fin n×Fin n)→Prop) (H:Bool→Fin n→U→Prop):Prop :=
    let RM:=fun W:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>typedMarkedOccurrenceResources W
    let state:=typedMarkedResourceState R H
    let RR:=ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W)
    let φ:=ordinaryMixedPhysicalResource (U:=U) π;
    ∀(L:Finset (PhysicalSampledCandidate (mixedCandidateResources RR) state))
    (hL:∀x∈L,∀y∈L,x≠y→Disjoint (physicalSampledCandidateSet φ (mixedCandidateResources RR) state x)
      (physicalSampledCandidateSet φ (mixedCandidateResources RR) state y)),
    let AM:=fun u:U=>OrdinaryPhysicalMarkedHub (K:=K) π d m RM state L u
    let AU:=fun u:U=>OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u
    let len:=fun (u:U) (a:AU u)=>longPaddedSeedExponent (ordinaryPhysicalUnmarkedPayload π d m RM state L u a).1+2
    let Q:=fun (u:U) (a:AU u)=>(ordinaryPhysicalUnmarkedPayload π d m RM state L u a).2
    let E:={e:Fin n×Fin n // R (Sum.inl e)}
    let S:={e:Fin n×Fin n // R (Sum.inr e)};
    ∀(u v:U),u≠v→
    ∀(W:AM u→MarkedWheel (fun e:E=>e.val.1) (fun e:E=>e.val.2)
      (fun e:S=>e.val.1) (fun e:S=>e.val.2) m π (3*d) (H false) (H true))
    (Z:AM v→MarkedWheel (fun e:E=>e.val.1) (fun e:E=>e.val.2)
      (fun e:S=>e.val.1) (fun e:S=>e.val.2) m π (3*d) (H false) (H true)),
    (∀a,(W a).1.val=(ordinaryPhysicalMarkedPayload π d m RM state L u a).1.val ∧ (W a).2.val=u)→
    (∀a,(Z a).1.val=(ordinaryPhysicalMarkedPayload π d m RM state L v a).1.val ∧ (Z a).2.val=v)→
    Disjoint (mixedWheelRimPack (len u) (Finset.univ.image W) (Q u))
      (mixedWheelRimPack (len v) (Finset.univ.image Z) (Q v))
end Oberwolfach
