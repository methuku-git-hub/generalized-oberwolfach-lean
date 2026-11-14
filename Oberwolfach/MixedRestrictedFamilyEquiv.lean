module

public import Oberwolfach.MixedApproximateResourceAggregation
public import Oberwolfach.ResourceRestriction

@[expose] public section
/-! Restricting a disjoint union of indexed families to the sampled ground
set is equivalent to restricting each family separately. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I V W:Type} [Fintype I] [Fintype V] [Fintype W] [DecidableEq I]
  [DecidableEq V] [DecidableEq W] {E:I→Type} [∀i,Fintype (E i)] [∀i,DecidableEq (E i)]

def mixedRestrictedFamilyEquiv (R:∀i,E i→Finset V) (e:W↪V):
    RestrictedResource (mixedCandidateResources R) e ≃ Σi,RestrictedResource (R i) e where
  toFun c := ⟨c.val.1,⟨c.val.2,c.property⟩⟩
  invFun c := ⟨⟨c.1,c.2.val⟩,c.2.property⟩
  left_inv c := by cases c with | mk x h => cases x; rfl
  right_inv c := by cases c with | mk i x => cases x; rfl

theorem mixed_restricted_component_test_mass
    (R:∀i,E i→Finset V) (e:W↪V) (w:∀i,E i→ℝ) (i:I) (g:∀j,E j→ℝ)
    (hzero:∀j,j≠i→∀c,g j c=0):
    (∑c:RestrictedResource (mixedCandidateResources R) e,
      g c.val.1 c.val.2*mixedCandidateWeight w c.val)=
    ∑c:RestrictedResource (R i) e,g i c.val*w i c.val := by
  let f := mixedRestrictedFamilyEquiv R e
  rw [←f.symm.sum_comp]
  simp only [Fintype.sum_sigma]
  dsimp [f,mixedRestrictedFamilyEquiv,mixedCandidateWeight]
  apply Finset.sum_eq_single i
  · intro j _ hji
    simp [hzero j hji]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim
end Oberwolfach
