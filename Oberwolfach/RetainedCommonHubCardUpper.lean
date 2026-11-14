module

public import Oberwolfach.OrdinaryCommonHubRootCard
public import Oberwolfach.RestrictedResourceSubsetCounts
public import Oberwolfach.BernoulliVertexSampling

@[expose] public section
/-! Restricting to a sample cannot create more than one ordinary spoke
root per host vertex at a fixed hub. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem retained_common_hub_card_le
    (state:(((V×V)⊕(V×V))⊕(Bool×V×U))→Bool) (u:U):
    let e:{v // v∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _;
    (restrictedResourceSubset e (ordinaryCommonHubSpokeRoots u)).card≤Fintype.card V :=by
  intro e
  have himage:(restrictedResourceSubset e (ordinaryCommonHubSpokeRoots u)).image e⊆ordinaryCommonHubSpokeRoots u:=by
    intro x hx
    obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hx
    exact (Finset.mem_filter.mp hv).2
  have hh:=Finset.card_le_card himage
  rw [Finset.card_image_of_injective _ e.injective,ordinary_common_hub_roots_card] at hh
  exact hh
end Oberwolfach
