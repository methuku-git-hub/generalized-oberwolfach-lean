module

public import Oberwolfach.MixedRestrictedHubMassDeviation
public import Oberwolfach.WeightedMatchingCountDeviation

@[expose] public section
/-! Exact transfer from raw restricted hub loads and counts to the number
of selected candidates in the family. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I V W U:Type} [Fintype I] [Fintype V] [Fintype W] [DecidableEq I]
  [DecidableEq V] [DecidableEq W] [DecidableEq U] {E:I→Type}
  [∀i,Fintype (E i)] [∀i,DecidableEq (E i)]

theorem mixed_matched_hub_test_count_deviation
    (R:∀i,E i→Finset V) (e:W↪V) (w:∀i,E i→ℝ) (i:I)
    (g:∀j,E j→ℝ) (hub:E i→U) (u:U) (S:Finset V) (r:ℕ)
    (hzero:∀j,j≠i→∀c,g j c=0)
    (hg:∀c,g i c=if hub c=u then 1 else 0)
    (hS:∀c,(R i c∩S).card=if hub c=u then r else 0)
    (η s n err countErr γ:ℝ) (hη:0≤η) (hγ:0≤γ)
    (hdeg:∀v∈restrictedResourceSubset e S,
      |hypergraphWeightedDegree (restrictedResourceSet (R i) e) (fun c=>w i c.val) v-η|≤err)
    (hcount:|((restrictedResourceSubset e S).card:ℝ)-s*n|≤countErr)
    (hweight:∀j c,0≤w j c) (hcoeff:∀j c,0≤g j c)
    (M:Finset (RestrictedResource (mixedCandidateResources R) e)):
    let mass:=∑c:RestrictedResource (mixedCandidateResources R) e,
      g c.val.1 c.val.2*mixedCandidateWeight w c.val
    let actual:=∑c∈M,g c.val.1 c.val.2
    let error:=(restrictedResourceSubset e S).card*err+η*countErr
    (1-γ)*mass≤actual→actual≤(1+γ)*mass→
    |(r:ℝ)*actual-η*s*n|≤error+γ*(|η*s*n|+error):=by
  intro mass actual error hlow hup
  have hmass:0≤mass:=by
    apply Finset.sum_nonneg
    intro c _
    exact mul_nonneg (hcoeff c.val.1 c.val.2) (hweight c.val.1 c.val.2)
  have hdev:=mixed_restricted_hub_test_mass_deviation R e w i g hub u S r hzero hg hS η s n err countErr hη hdeg hcount
  exact weighted_matching_count_deviation r mass actual (η*s*n) error γ (Nat.cast_nonneg _) hmass hγ hdev hlow hup
end Oberwolfach
