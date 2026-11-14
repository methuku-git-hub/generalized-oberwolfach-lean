module

public import Oberwolfach.OrdinaryPhysicalMatchingAllHubPacks

@[expose] public section
/-! The specific marked wheels already extracted from one physical matching
produce pairwise-disjoint mixed rim packs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem ordinary_physical_matching_chosen_packs_disjoint (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (R:(Fin n×Fin n)⊕(Fin n×Fin n)→Prop) (H:Bool→Fin n→U→Prop):
    let RM:=fun W:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>typedMarkedOccurrenceResources W
    let state:=typedMarkedResourceState R H
    let RR:=ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W)
    let φ:=ordinaryMixedPhysicalResource (U:=U) π;
    ∀(L:Finset (PhysicalSampledCandidate (mixedCandidateResources RR) state))
    (hL:∀x∈L,∀y∈L,x≠y→Disjoint (physicalSampledCandidateSet φ (mixedCandidateResources RR) state x)
      (physicalSampledCandidateSet φ (mixedCandidateResources RR) state y))
    (W:∀u,OrdinaryPhysicalMarkedHub (K:=K) π d m RM state L u→
      MarkedWheel (fun e:{e:Fin n×Fin n // R (Sum.inl e)}=>e.val.1) (fun e=>e.val.2)
      (fun e:{e:Fin n×Fin n // R (Sum.inr e)}=>e.val.1) (fun e=>e.val.2) m π (3*d) (H false) (H true))
    (hW:∀u a,(W u a).1.val=(ordinaryPhysicalMarkedPayload π d m RM state L u a).1.val ∧ (W u a).2.val=u),
    let Pack:=fun u=>mixedWheelRimPack
      (fun j:OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u=>longPaddedSeedExponent (ordinaryPhysicalUnmarkedPayload π d m RM state L u j).1+2)
      (Finset.univ.image (W u)) (fun j=>(ordinaryPhysicalUnmarkedPayload π d m RM state L u j).2);
    ∀u v,u≠v→Disjoint (Pack u) (Pack v):=by
  intro RM state RR φ L hL W hW Pack
  apply ordinary_physical_matching_all_hub_packs_disjoint (K:=K) π d m R H L hL Pack
  intro u
  exact ⟨W u,hW u,rfl⟩
end Oberwolfach
