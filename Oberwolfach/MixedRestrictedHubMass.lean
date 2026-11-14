module

public import Oberwolfach.MixedRestrictedFamilyEquiv
public import Oberwolfach.RestrictedHubTestMass

@[expose] public section
/-! A test for one family and one hub has exactly the weight encoded by
the retained spoke degrees of that family. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I V W U:Type} [Fintype I] [Fintype V] [Fintype W] [DecidableEq I]
  [DecidableEq V] [DecidableEq W] [DecidableEq U] {E:I→Type}
  [∀i,Fintype (E i)] [∀i,DecidableEq (E i)]

theorem mixed_restricted_hub_test_mass_identity
    (R:∀i,E i→Finset V) (e:W↪V) (w:∀i,E i→ℝ) (i:I)
    (g:∀j,E j→ℝ) (hub:E i→U) (u:U) (S:Finset V) (r:ℕ)
    (hzero:∀j,j≠i→∀c,g j c=0)
    (hg:∀c,g i c=if hub c=u then 1 else 0)
    (hS:∀c,(R i c∩S).card=if hub c=u then r else 0):
    (∑v∈restrictedResourceSubset e S,
      hypergraphWeightedDegree (restrictedResourceSet (R i) e) (fun c=>w i c.val) v)=
    (r:ℝ)*∑c:RestrictedResource (mixedCandidateResources R) e,
      g c.val.1 c.val.2*mixedCandidateWeight w c.val := by
  rw [mixed_restricted_component_test_mass R e w i g hzero]
  have hh:=restricted_resource_hub_test_mass_identity (R i) e (w i) hub u S r hS
  convert hh using 1
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  rw [hg]
  split_ifs <;> simp
theorem mixed_restricted_hub_test_mass_lower
    (R:∀i,E i→Finset V) (e:W↪V) (w:∀i,E i→ℝ) (i:I)
    (g:∀j,E j→ℝ) (hub:E i→U) (u:U) (S:Finset V) (r:ℕ)
    (hr:0<r) (hzero:∀j,j≠i→∀c,g j c=0)
    (hg:∀c,g i c=if hub c=u then 1 else 0)
    (hS:∀c,(R i c∩S).card=if hub c=u then r else 0)
    (a:ℝ) (hdeg:∀v∈restrictedResourceSubset e S,
      a≤hypergraphWeightedDegree (restrictedResourceSet (R i) e) (fun c=>w i c.val) v):
    a*((restrictedResourceSubset e S).card:ℝ)/(r:ℝ)≤
      ∑c:RestrictedResource (mixedCandidateResources R) e,
        g c.val.1 c.val.2*mixedCandidateWeight w c.val := by
  rw [mixed_restricted_component_test_mass R e w i g hzero]
  have hh:=restricted_resource_hub_test_mass_lower (R i) e (w i) hub u S r hr hS a hdeg
  convert hh using 1
  congr 1
  funext c
  rw [hg]
  split_ifs <;> simp
end Oberwolfach
