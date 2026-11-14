module

public import Oberwolfach.OrdinaryPhysicalUnmarkedPayload
public import Oberwolfach.OrdinaryMixedNonePayload

@[expose] public section
/-! Extract the marked candidate identifiers and their exact typed resources
from the same physical matching used for the ordinary wheels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

abbrev OrdinaryPhysicalMarkedHub (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (RM:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→Finset (((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U)))
    (state:(((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U))→Bool)
    (L:Finset (PhysicalSampledCandidate (mixedCandidateResources
      (ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W))) state))
    (u:U):Type :=
  ↥(L.filter (fun x=>x.val.1.isNone ∧ ordinaryMixedGenericWheelHub (U:=U) π (3*d) m longPaddedSeedExponent x.val.1 x.val.2=u))

def ordinaryPhysicalMarkedPayload (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (RM:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→Finset (((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U)))
    (state:(((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U))→Bool)
    (L:Finset (PhysicalSampledCandidate (mixedCandidateResources
      (ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W))) state))
    (u:U) (a:OrdinaryPhysicalMarkedHub (K:=K) π d m RM state L u):
    MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True) :=
  ordinaryMixedNonePayload ⟨a.val.val,(Finset.mem_filter.mp a.property).2.1⟩

theorem ordinary_physical_marked_payload_hub (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (RM:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→Finset (((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U)))
    (state:(((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U))→Bool)
    (L:Finset (PhysicalSampledCandidate (mixedCandidateResources
      (ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W))) state))
    (u:U) (a:OrdinaryPhysicalMarkedHub (K:=K) π d m RM state L u):
    (ordinaryPhysicalMarkedPayload π d m RM state L u a).2.val=u :=by
  have heq:=ordinary_mixed_none_payload_original ⟨a.val.val,(Finset.mem_filter.mp a.property).2.1⟩
  have hh:=congrArg (fun c=>ordinaryMixedGenericWheelHub (U:=U) π (3*d) m longPaddedSeedExponent c.1 c.2) heq
  have hu:ordinaryMixedGenericWheelHub (U:=U) π (3*d) m longPaddedSeedExponent a.val.val.1 a.val.val.2=u:=
    (Finset.mem_filter.mp a.property).2.2
  exact hh.symm.trans hu

theorem ordinary_physical_marked_payload_resources (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (RM:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→Finset (((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U)))
    (state:(((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U))→Bool)
    (L:Finset (PhysicalSampledCandidate (mixedCandidateResources
      (ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W))) state))
    (u:U) (a:OrdinaryPhysicalMarkedHub (K:=K) π d m RM state L u):
    mixedCandidateResources (ordinaryMixedGenericResources RM
      (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W)) a.val.val =
      RM (ordinaryPhysicalMarkedPayload π d m RM state L u a) :=by
  have h:=ordinary_mixed_none_payload_original ⟨a.val.val,(Finset.mem_filter.mp a.property).2.1⟩
  rw [h]
  rfl
end Oberwolfach
