module

public import Oberwolfach.OrdinaryPhysicalResourceToFinite
public import Oberwolfach.PhysicalSampledMatchingImages

@[expose] public section
/-! A physical matching remains disjoint after changing from unordered-pair
resources to the finite-set representation used by wheel packing. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U C:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U] [Fintype C]

theorem ordinary_physical_matching_finite_images_disjoint
    (π:Equiv.Perm V) (R:C→Finset (((V×V)⊕(V×V))⊕(Bool×V×U)))
    (state:(((V×V)⊕(V×V))⊕(Bool×V×U))→Bool)
    (L:Finset (PhysicalSampledCandidate R state)):
    let φ:=ordinaryMixedPhysicalResource (U:=U) π;
    (∀x∈L,∀y∈L,x≠y→Disjoint (physicalSampledCandidateSet φ R state x)
      (physicalSampledCandidateSet φ R state y))→
    ∀x∈L,∀y∈L,x≠y→Disjoint ((R x.val).image (markedSeedPhysicalMap π))
      ((R y.val).image (markedSeedPhysicalMap π)) :=by
  intro φ hL x hx y hy hxy
  have h:=physical_sampled_matching_images_disjoint φ R state L hL x hx y hy hxy
  have hh:=(Finset.disjoint_image (ordinary_physical_resource_to_finite_injective (V:=V) (U:=U))).mpr h
  simp only [Finset.image_image] at hh
  dsimp only [φ] at hh
  rw [ordinary_physical_resource_to_finite_comp] at hh
  exact hh
end Oberwolfach
