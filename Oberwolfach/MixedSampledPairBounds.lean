module

public import Oberwolfach.MixedApproximateResourceAggregation

@[expose] public section
/-! A mixed physical candidate family retains its componentwise pair bounds
after arbitrary sampling or deletion of candidates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I V:Type} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]
  {E:I→Type} [∀i,Fintype (E i)] [∀i,DecidableEq (E i)]

theorem mixed_sampled_pair_bound
    (R:∀i,E i→Finset V) (w:∀i,E i→ℝ) (hw:∀i c,0≤w i c)
    (K:I→ℝ) (n:ℝ)
    (h:∀i u v,u≠v→(∑e:E i,if u∈R i e ∧ v∈R i e then w i e else 0)≤K i/n)
    (T:Finset (Σi,E i)) (u v:V) (huv:u≠v):
    (∑e∈T,if u∈mixedCandidateResources R e ∧ v∈mixedCandidateResources R e
      then mixedCandidateWeight w e else 0)≤(∑i,K i)/n :=by
  have hh:=mixed_candidate_codegree_from_components R w K n h u v huv
  apply (Finset.sum_le_univ_sum_of_nonneg (s:=T) (fun e=>?_) : _).trans hh
  split_ifs
  · exact hw _ _
  · exact le_refl 0
end Oberwolfach
