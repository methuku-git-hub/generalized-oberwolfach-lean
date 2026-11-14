module

public import Oberwolfach.LongRetainedPaddedIndexSet
public import Oberwolfach.OrdinaryMixedSomeResources
public import Oberwolfach.OrdinaryAssignedRetainedHubTests
public import Oberwolfach.PhysicalSampledMatchingImages

@[expose] public section
/-! Extract actual unmarked wheel tuples at a fixed hub from a physical
matching, preserving the candidate tag and physical resource image. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

abbrev OrdinaryPhysicalUnmarkedHub (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (RM:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→Finset (((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U)))
    (state:(((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U))→Bool)
    (L:Finset (PhysicalSampledCandidate (mixedCandidateResources
      (ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W))) state))
    (u:U):Type :=
  ↥(L.filter (fun x=>x.val.1.isSome ∧ ordinaryMixedGenericWheelHub (U:=U) π (3*d) m longPaddedSeedExponent x.val.1 x.val.2=u))

def ordinaryPhysicalUnmarkedPayload (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (RM:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→Finset (((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U)))
    (state:(((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U))→Bool)
    (L:Finset (PhysicalSampledCandidate (mixedCandidateResources
      (ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W))) state))
    (u:U) (a:OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u):
    Σi:Fin K,OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2) :=
  ordinaryMixedSomePayload ⟨a.val.val,(Finset.mem_filter.mp a.property).2.1⟩

theorem ordinary_physical_unmarked_payload_index (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (RM:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→Finset (((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U)))
    (state:(((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U))→Bool)
    (L:Finset (PhysicalSampledCandidate (mixedCandidateResources
      (ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W))) state))
    (u:U) (a:OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u) (i₀:Fin K):
    a.val.val.1.getD i₀=(ordinaryPhysicalUnmarkedPayload π d m RM state L u a).1 :=by
  exact ordinary_mixed_some_payload_index ⟨a.val.val,(Finset.mem_filter.mp a.property).2.1⟩ i₀

theorem ordinary_physical_unmarked_payload_hub (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (RM:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→Finset (((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U)))
    (state:(((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U))→Bool)
    (L:Finset (PhysicalSampledCandidate (mixedCandidateResources
      (ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W))) state))
    (u:U) (a:OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u):
    (ordinaryPhysicalUnmarkedPayload π d m RM state L u a).2.2=u :=by
  have heq:=ordinary_mixed_some_payload_original ⟨a.val.val,(Finset.mem_filter.mp a.property).2.1⟩
  have hh:=congrArg (fun c=>ordinaryMixedGenericWheelHub (U:=U) π (3*d) m longPaddedSeedExponent c.1 c.2) heq
  have hu:ordinaryMixedGenericWheelHub (U:=U) π (3*d) m longPaddedSeedExponent a.val.val.1 a.val.val.2=u:=
    (Finset.mem_filter.mp a.property).2.2
  exact hh.symm.trans hu
end Oberwolfach
