module

public import Oberwolfach.MixedHubIndicatorTest

@[expose] public section
/-! In the selected matching, the weighted test sum is literally the number
of selected candidates of the specified family and hub. -/
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

theorem mixed_matched_family_hub_count
    (R:∀i,E i→Finset V) (e:W↪V) (w:∀i,E i→ℝ) (i:I)
    (hub:∀j,E j→U) (u:U) (S:Finset V) (r:ℕ)
    (hS:∀c,(R i c∩S).card=if hub i c=u then r else 0)
    (η s n err countErr γ:ℝ) (hη:0≤η) (hγ:0≤γ)
    (hdeg:∀v∈restrictedResourceSubset e S,
      |hypergraphWeightedDegree (restrictedResourceSet (R i) e) (fun c=>w i c.val) v-η|≤err)
    (hcount:|((restrictedResourceSubset e S).card:ℝ)-s*n|≤countErr)
    (hweight:∀j c,0≤w j c)
    (M:Finset (RestrictedResource (mixedCandidateResources R) e)):
    let g:=mixedHubIndicator hub i u
    let mass:=∑c:RestrictedResource (mixedCandidateResources R) e,
      g c.val.1 c.val.2*mixedCandidateWeight w c.val
    let actual:=∑c∈M,g c.val.1 c.val.2
    let error:=(restrictedResourceSubset e S).card*err+η*countErr
    (1-γ)*mass≤actual→actual≤(1+γ)*mass→
    |(r:ℝ)*((M.filter (fun c=>c.val.1=i ∧ hub c.val.1 c.val.2=u)).card:ℝ)-η*s*n|
      ≤error+γ*(|η*s*n|+error):=by
  intro g mass actual error hlow hup
  have hc:actual=((M.filter (fun c=>c.val.1=i ∧ hub c.val.1 c.val.2=u)).card:ℝ):=by
    exact mixed_hub_indicator_sum_is_card Subtype.val hub i u M
  have h:=mixed_matched_hub_test_count_deviation R e w i g (hub i) u S r
    (mixed_hub_indicator_other_family hub i u) (mixed_hub_indicator_same_family hub i u) hS
    η s n err countErr γ hη hγ hdeg hcount hweight (fun j c=>(mixed_hub_indicator_nonnegative hub i u j c).1) M hlow hup
  change |(r:ℝ)*actual-η*s*n|≤error+γ*(|η*s*n|+error) at h
  rw [hc] at h
  exact h
end Oberwolfach
