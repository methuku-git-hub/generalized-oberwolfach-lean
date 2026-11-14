module

public import Oberwolfach.FiniteWeightedBadUnion

@[expose] public section
/-! Two reusable rewrites for weighted bad-event unions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finite_weighted_value_union {I J:Type} [Fintype I] [DecidableEq J]
    (S:Finset J) (anchor:I→Prop) (f:I→J) (w:I→ℝ) (hw:∀i,0≤w i):
    (∑i,if anchor i ∧ f i∈S then w i else 0)≤
      ∑j∈S,∑i,if anchor i ∧ f i=j then w i else 0:=by
  have hh:=finite_weighted_bad_union S anchor (fun i j=>f i=j) w hw
  have he (i:I):(∃j∈S,f i=j) ↔ f i∈S:=by
    constructor
    · rintro ⟨j,hj,he⟩
      simpa only [he] using hj
    · intro hi
      exact ⟨f i,hi,rfl⟩
  simp only [he] at hh
  convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _

theorem finite_weighted_drop_impossible {I:Type} [Fintype I]
    (anchor bad other:I→Prop) (w:I→ℝ) (hbad:∀i,anchor i→¬bad i):
    (∑i,if anchor i ∧ (bad i ∨ other i) then w i else 0)=
      ∑i,if anchor i ∧ other i then w i else 0:=by
  apply Finset.sum_congr rfl
  intro i _
  by_cases ha:anchor i
  · have hb:=hbad i ha
    simp only [ha,hb,false_or,true_and]
  · simp only [ha,false_and,if_false]
end Oberwolfach
