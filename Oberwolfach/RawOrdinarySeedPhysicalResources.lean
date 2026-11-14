module

public import Oberwolfach.RawMarkedSeedPhysicalResources
public import Oberwolfach.OrderedOrdinaryWheelResources
public import Oberwolfach.MarkedOrdinaryResourceLoads

@[expose] public section
/-! Physical rim and spoke resources of an ordered ordinary seed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]

def ordinaryWheelPhysicalResources {π:Equiv.Perm V} {b r:ℕ}
    (W:OrderedOrdinaryWheel (U:=U) π b r):Finset (Finset V⊕(V×U)) :=
  Finset.univ.image (fun i:Fin r=>Sum.inl ({W.1.val i,W.1.val (cycleNext i)}:Finset V)) ∪
    Finset.univ.image (fun i:Fin r=>Sum.inr (W.1.val i,W.2))

theorem ordinary_seed_physical_resource_image (π:Equiv.Perm V) (b r:ℕ)
    (W:OrderedOrdinaryWheel (U:=U) π b r):
    ((orderedOrdinaryResources W).map ordinaryMarkedResourceEmbedding).image (markedSeedPhysicalMap π)=
      ordinaryWheelPhysicalResources W:=by
  ext z
  simp only [orderedOrdinaryResources,Finset.map_union,Finset.image_union,ordinaryWheelPhysicalResources]
  simp [Finset.map_eq_image,Finset.image_image,ordinaryMarkedResourceEmbedding,
    orderedOrdinaryResourceEmbedding,markedSeedPhysicalMap,physicalResourceToFinite,
    typedResourcePhysical,markedResourceTypeEquiv,Sym2.toFinset_mk_eq,Function.comp_def]
end Oberwolfach
