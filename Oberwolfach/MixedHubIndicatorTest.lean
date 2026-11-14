module

public import Oberwolfach.MixedMatchedHubDeviation

@[expose] public section
/-! The actual matching test is the indicator of one family and one hub. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I U:Type} [DecidableEq I] [DecidableEq U] {E:I→Type}

def mixedHubIndicator (hub:∀i,E i→U) (i:I) (u:U):∀j,E j→ℝ:=
  fun j c=>if j=i ∧ hub j c=u then 1 else 0

theorem mixed_hub_indicator_nonnegative (hub:∀i,E i→U) (i:I) (u:U) (j:I) (c:E j):
    0≤mixedHubIndicator hub i u j c ∧ mixedHubIndicator hub i u j c≤1 :=by
  unfold mixedHubIndicator
  split_ifs <;> norm_num

theorem mixed_hub_indicator_other_family (hub:∀i,E i→U) (i:I) (u:U):
    ∀j,j≠i→∀c,mixedHubIndicator hub i u j c=0 :=by
  intro j hj c
  simp [mixedHubIndicator,hj]

theorem mixed_hub_indicator_same_family (hub:∀i,E i→U) (i:I) (u:U) (c:E i):
    mixedHubIndicator hub i u i c=if hub i c=u then 1 else 0 :=by
  simp [mixedHubIndicator]

theorem mixed_hub_indicator_sum_is_card {C:Type} [DecidableEq C]
    (v:C→Σj,E j) (hub:∀i,E i→U) (i:I) (u:U) (M:Finset C):
    (∑c∈M,mixedHubIndicator hub i u (v c).1 (v c).2)=
      ((M.filter (fun c=>(v c).1=i ∧ hub (v c).1 (v c).2=u)).card:ℝ):=by
  classical
  simp [mixedHubIndicator,Finset.sum_ite,Finset.filter_filter]
end Oberwolfach
