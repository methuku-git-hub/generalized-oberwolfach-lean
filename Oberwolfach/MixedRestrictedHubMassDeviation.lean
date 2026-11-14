module

public import Oberwolfach.ResourceHubMassDeviation
public import Oberwolfach.MixedRestrictedFamilyEquiv
public import Oberwolfach.RestrictedResourceSubsetCounts

@[expose] public section
/-! The actual mixed-family hub test has the prescribed mass up to the
sum of its root-load and raw spoke-count errors. -/
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

theorem mixed_restricted_hub_test_mass_deviation
    (R:∀i,E i→Finset V) (e:W↪V) (w:∀i,E i→ℝ) (i:I)
    (g:∀j,E j→ℝ) (hub:E i→U) (u:U) (S:Finset V) (r:ℕ)
    (hzero:∀j,j≠i→∀c,g j c=0)
    (hg:∀c,g i c=if hub c=u then 1 else 0)
    (hS:∀c,(R i c∩S).card=if hub c=u then r else 0)
    (η s n err countErr:ℝ) (hη:0≤η)
    (hdeg:∀v∈restrictedResourceSubset e S,
      |hypergraphWeightedDegree (restrictedResourceSet (R i) e) (fun c=>w i c.val) v-η|≤err)
    (hcount:|((restrictedResourceSubset e S).card:ℝ)-s*n|≤countErr):
    |(r:ℝ)*(∑c:RestrictedResource (mixedCandidateResources R) e,
      g c.val.1 c.val.2*mixedCandidateWeight w c.val)-η*s*n|≤
        (restrictedResourceSubset e S).card*err+η*countErr := by
  rw [mixed_restricted_component_test_mass R e w i g hzero]
  have hS':∀c:RestrictedResource (R i) e,
      ((restrictedResourceSet (R i) e c)∩restrictedResourceSubset e S).card=
        if hub c.val=u then r else 0:=by
    intro c
    rw [restricted_resource_subset_card]
    exact hS c.val
  have hh:=resource_hub_test_mass_deviation (restrictedResourceSet (R i) e)
    (fun c=>w i c.val) (fun c=>hub c.val) u (restrictedResourceSubset e S) r hS'
    η s n err countErr hη hdeg hcount
  have hmassEq:(∑c:RestrictedResource (R i) e,g i c.val*w i c.val)=
      ∑c:RestrictedResource (R i) e,if hub c.val=u then w i c.val else 0 := by
    apply Finset.sum_congr rfl
    intro c _
    rw [hg]
    split_ifs <;> simp
  rw [hmassEq]
  exact hh
end Oberwolfach
