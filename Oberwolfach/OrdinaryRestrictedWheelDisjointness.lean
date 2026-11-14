module

public import Oberwolfach.RestrictedResourceMatchingReflect
public import Oberwolfach.OrderedOrdinaryWheelResources
public import Oberwolfach.MarkedOrdinaryResourceLoads

@[expose] public section
/-! Ordinary wheels with disjoint sampled typed resources have disjoint
original rim-and-spoke resource sets, including across different lengths. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U X:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
  [Fintype X] [DecidableEq X]

theorem ordinary_restricted_wheels_original_resources_disjoint
    (π:Equiv.Perm V) (b r s:ℕ)
    (e:X↪(((V×V)⊕(V×V))⊕(Bool×V×U)))
    (A:RestrictedResource (fun W:OrderedOrdinaryWheel (U:=U) π b r=>
      (orderedOrdinaryResources W).map ordinaryMarkedResourceEmbedding) e)
    (B:RestrictedResource (fun W:OrderedOrdinaryWheel (U:=U) π b s=>
      (orderedOrdinaryResources W).map ordinaryMarkedResourceEmbedding) e)
    (h:Disjoint
      (restrictedResourceSet (fun W:OrderedOrdinaryWheel (U:=U) π b r=>
        (orderedOrdinaryResources W).map ordinaryMarkedResourceEmbedding) e A)
      (restrictedResourceSet (fun W:OrderedOrdinaryWheel (U:=U) π b s=>
        (orderedOrdinaryResources W).map ordinaryMarkedResourceEmbedding) e B)):
    Disjoint (orderedOrdinaryResources A.val) (orderedOrdinaryResources B.val) :=by
  have hA:=restrictedResourceSet_image
    (fun W:OrderedOrdinaryWheel (U:=U) π b r=>(orderedOrdinaryResources W).map ordinaryMarkedResourceEmbedding) e A
  have hB:=restrictedResourceSet_image
    (fun W:OrderedOrdinaryWheel (U:=U) π b s=>(orderedOrdinaryResources W).map ordinaryMarkedResourceEmbedding) e B
  have hmap:Disjoint ((orderedOrdinaryResources A.val).map ordinaryMarkedResourceEmbedding)
      ((orderedOrdinaryResources B.val).map ordinaryMarkedResourceEmbedding):=by
    rw [←hA,←hB]
    exact (Finset.disjoint_image e.injective).mpr h
  exact (Finset.disjoint_map ordinaryMarkedResourceEmbedding).mp hmap
end Oberwolfach
