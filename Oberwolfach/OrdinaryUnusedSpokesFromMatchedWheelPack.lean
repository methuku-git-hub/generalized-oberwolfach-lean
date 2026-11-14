module

public import Oberwolfach.OrdinaryUnusedSpokesFromPhysicalRow
public import Oberwolfach.OrdinaryMatchedSpokeWheelPack
public import Oberwolfach.OrdinaryPhysicalCandidateSpokeHub
public import Oberwolfach.OrdinaryMarkedTupleVertexInRim

@[expose] public section

/-! A covered physical spoke belongs to the rim-vertex set of one of the
same hub's wheels in the coherent matching. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option synthInstance.maxSize 65536
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem ordinary_unused_spokes_from_matched_wheel_pack
    (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (Rim:(Fin n×Fin n)⊕(Fin n×Fin n)→Prop) (H:Bool→Fin n→U→Prop):
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
    let len:=fun a:OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u=>
      longPaddedSeedExponent (ordinaryPhysicalUnmarkedPayload π d m RM state L u a).1+2
    let Q:=fun a:OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u=>
      (ordinaryPhysicalUnmarkedPayload π d m RM state L u a).2
    let Pack:=mixedWheelRimPack len (Finset.univ.image W) Q;
    ∀Old:Finset (Fin n),
      (∀edge∈Pack,∀v∈edge,v∈Old)→
      ((Finset.univ.filter (fun v=>H false v u))\Old).card≤
        ((physicalSampledRow φ state (ordinaryPhysicalRow (.inr (.inr u))))\
          L.biUnion (physicalSampledCandidateSet φ (mixedCandidateResources RR) state)).card :=by
  intro RM state RR φ L u W hW len Q Pack Old hOld
  apply ordinary_unused_spokes_le_physical_row (K:=K) π d m Rim H L u Old
  intro v hv c hc x hx hcx
  obtain ⟨edge,he,hvEdge⟩:=ordinary_matched_spoke_in_wheel_pack (K:=K) π d m Rim H L u W hW c hc x v hx hcx
  exact hOld edge he v hvEdge
end Oberwolfach
