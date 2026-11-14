module

public import Oberwolfach.ResourceSubsetWeightedMass
public import Oberwolfach.RestrictedResourceSubsetCounts

@[expose] public section
/-! Hub coefficient-test masses of surviving candidates are exactly the
weighted degrees on the retained hub-spoke resources. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W C U:Type} [Fintype V] [Fintype W] [Fintype C] [DecidableEq V] [DecidableEq W]
  [DecidableEq C] [DecidableEq U]

theorem restricted_resource_hub_test_mass_identity
    (R:C→Finset V) (e:W↪V) (w:C→ℝ) (hub:C→U) (u:U) (S:Finset V) (r:ℕ)
    (hS:∀c,(R c∩S).card=if hub c=u then r else 0):
    (∑v∈restrictedResourceSubset e S,
      hypergraphWeightedDegree (restrictedResourceSet R e) (fun c=>w c.val) v)=
      (r:ℝ)*∑c:RestrictedResource R e,if hub c.val=u then w c.val else 0 := by
  apply resource_hub_test_mass_identity (restrictedResourceSet R e) (fun c=>w c.val)
    (fun c=>hub c.val) u (restrictedResourceSubset e S) r
  intro c
  rw [restricted_resource_subset_card]
  exact hS c.val

theorem restricted_resource_hub_test_mass_lower
    (R:C→Finset V) (e:W↪V) (w:C→ℝ) (hub:C→U) (u:U) (S:Finset V) (r:ℕ)
    (hr:0<r) (hS:∀c,(R c∩S).card=if hub c=u then r else 0)
    (a:ℝ) (hdeg:∀v∈restrictedResourceSubset e S,
      a≤hypergraphWeightedDegree (restrictedResourceSet R e) (fun c=>w c.val) v):
    a*((restrictedResourceSubset e S).card:ℝ)/(r:ℝ)≤
      ∑c:RestrictedResource R e,if hub c.val=u then w c.val else 0 := by
  apply resource_hub_test_mass_lower (restrictedResourceSet R e) (fun c=>w c.val)
    (fun c=>hub c.val) u (restrictedResourceSubset e S) r hr _ a hdeg
  intro c
  rw [restricted_resource_subset_card]
  exact hS c.val
end Oberwolfach
