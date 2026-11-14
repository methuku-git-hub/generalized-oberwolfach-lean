module

public import Oberwolfach.ResourceRootOmittedLoads

@[expose] public section

/-! Compare fixed resource sums through an explicit exceptional family of
candidates. The coefficients and the omitted root remain unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finite_weighted_exception_union {I Z:Type*} [Fintype I]
    (T:Finset Z) (w:I→ℝ) (hw:∀ i,0≤w i) (P:I→Prop) (Q:Z→I→Prop):
    (∑ i,if P i∧(∃ z∈T,Q z i) then w i else 0)≤
      ∑ z∈T,∑ i,if P i∧Q z i then w i else 0:=by
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i _
  have hnon:∀ z∈T,0≤(if P i∧Q z i then w i else 0):=by
    intro z _;split_ifs <;> first | exact hw i | rfl
  by_cases he:P i∧(∃ z∈T,Q z i)
  · obtain ⟨z,hz,hQ⟩:=he.2
    rw [if_pos he]
    have hh:=Finset.single_le_sum hnon hz
    rw [if_pos (show P i∧Q z i from ⟨he.1,hQ⟩)] at hh
    exact hh
  · rw [if_neg he]
    exact Finset.sum_nonneg hnon

theorem resourceRootOmittedLoad_exceptional_candidates {I A:Type*}
    [Fintype I] [Fintype A] [DecidableEq A]
    (R:I→Finset A) (w:I→ℝ) (hw:∀ i,0≤w i)
    (keep keep':A→Prop) (Good:I→Prop)
    (hsame:∀ i,Good i→∀ a∈R i,keep a↔keep' a) (e:A):
    |resourceRootOmittedLoad R w keep' e-resourceRootOmittedLoad R w keep e|≤
      ∑ i,if e∈R i∧¬Good i then w i else 0:=by
  unfold resourceRootOmittedLoad
  rw [←Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  by_cases he:e∈R i
  · by_cases hg:Good i
    · have hh:(∀ a∈R i,a≠e→keep a)↔(∀ a∈R i,a≠e→keep' a):=by
        constructor
        · intro h a ha hne;exact (hsame i hg a ha).mp (h a ha hne)
        · intro h a ha hne;exact (hsame i hg a ha).mpr (h a ha hne)
      have hz:(if e∈R i∧(∀ a∈R i,a≠e→keep' a) then w i else 0)=
          (if e∈R i∧(∀ a∈R i,a≠e→keep a) then w i else 0):=by
        by_cases h:∀ a∈R i,a≠e→keep a
        · rw [if_pos ⟨he,hh.mp h⟩,if_pos ⟨he,h⟩]
        · rw [if_neg (fun h'=>h (hh.mpr h'.2)),if_neg (fun h'=>h h'.2)]
      rw [hz,sub_self,abs_zero,if_neg (fun h=>h.2 hg)]
    · simp only [if_pos (show e∈R i∧¬Good i from ⟨he,hg⟩)]
      split_ifs <;> simp only [sub_self,abs_zero,sub_zero,zero_sub,abs_neg,abs_of_nonneg (hw i)] <;> first | rfl | exact hw i
  · simp only [he,false_and,ite_false,sub_self,abs_zero,le_refl]

end Oberwolfach
