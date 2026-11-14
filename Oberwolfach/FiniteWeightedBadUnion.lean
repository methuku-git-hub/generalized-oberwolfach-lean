module

public import Oberwolfach.FiniteConfigurationLoss

@[expose] public section
/-! A weighted union bound for a finite family of forbidden events. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finite_weighted_bad_union {I J:Type} [Fintype I] [DecidableEq J]
    (S:Finset J) (anchor:I→Prop) (bad:I→J→Prop) (w:I→ℝ) (hw:∀i,0≤w i):
    (∑i,if anchor i ∧ ∃j∈S,bad i j then w i else 0)≤
      ∑j∈S,∑i,if anchor i ∧ bad i j then w i else 0:=by
  have hp (i:I):
      (if anchor i ∧ ∃j∈S,bad i j then w i else 0)≤
        ∑j∈S,if anchor i ∧ bad i j then w i else 0:=by
    by_cases h:anchor i ∧ ∃j∈S,bad i j
    · rw [if_pos h]
      obtain ⟨ha,j,hj,hij⟩:=h
      have hh:=Finset.single_le_sum (s:=S) (a:=j)
        (f:=fun j=>if anchor i ∧ bad i j then w i else 0)
        (fun j _=>by split_ifs <;> simp_all) hj
      simpa only [ha,hij,and_self,ite_true] using hh
    · rw [if_neg h]
      apply Finset.sum_nonneg
      intro j _
      split_ifs <;> simp_all
  calc
    _ ≤ ∑i,∑j∈S,if anchor i ∧ bad i j then w i else 0:=Finset.sum_le_sum (fun i _=>hp i)
    _ = _:=by rw [Finset.sum_comm]

theorem finite_weighted_two_bad_union {I:Type} [Fintype I]
    (anchor bad₁ bad₂:I→Prop) (w:I→ℝ) (hw:∀i,0≤w i):
    (∑i,if anchor i ∧ (bad₁ i ∨ bad₂ i) then w i else 0)≤
      (∑i,if anchor i ∧ bad₁ i then w i else 0)+
      (∑i,if anchor i ∧ bad₂ i then w i else 0):=by
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  by_cases ha:anchor i <;> by_cases hb:bad₁ i <;> by_cases hc:bad₂ i <;> simp [ha,hb,hc,hw i]
end Oberwolfach
