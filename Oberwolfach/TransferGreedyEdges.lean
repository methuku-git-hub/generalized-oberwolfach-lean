module

public import Oberwolfach.TransferGreedyOrder
public import Oberwolfach.CycleCopies

@[expose] public section

/-! The ordered construction contains the base cycle, each row cycle,
and each row cycle with its base vertex replaced by the prescribed root. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

abbrev transferConstructionGraph (r : ℕ) (hr : 3 ≤ r) :=
  predecessorGraph (transferPredecessors r) (transferPredecessors_earlier r hr)

abbrev transferRowStart (r i : ℕ) := r+1+i*(r-1)

theorem transferPredecessors_row_formula (r i j : ℕ) (hr : 3 ≤ r) (hj : j < r-1) :
    transferPredecessors r (transferRowStart r i+j)=
      if j=0 then {0,i+1} else if j=1 then
        if r=3 then {0,i+1,transferRowStart r i} else {0,i+1}
      else {if j=2 then transferRowStart r i else transferRowStart r i+j-1}∪
        (if j=r-2 then {transferRowStart r i+1} else ∅) := by
  have hz : transferRowStart r i+j≠0 := by unfold transferRowStart;omega
  have hzr : ¬transferRowStart r i+j≤r := by unfold transferRowStart;omega
  have hsub : transferRowStart r i+j-r-1=(r-1)*i+j := by simp only [transferRowStart,Nat.mul_comm];omega
  have hdiv : ((r-1)*i+j)/(r-1)=i := by
    rw [Nat.mul_add_div (by omega),Nat.div_eq_of_lt hj,Nat.add_zero]
  have hmod : ((r-1)*i+j)%(r-1)=j := by rw [Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt hj]
  unfold transferPredecessors
  rw [if_neg hz,if_neg hzr]
  dsimp only
  rw [hsub,hdiv,hmod]
  split_ifs <;> ext x <;> simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,Nat.add_sub_cancel]
  all_goals omega

theorem transferConstructionGraph_base_step (r a : ℕ) (hr : 3 ≤ r)
    (ha : 0 < a) (har : a < r) : (transferConstructionGraph r hr).Adj a (a+1) := by
  apply Or.inl
  unfold transferPredecessors
  have hz : a+1≠0 := by omega
  have hle : a+1≤r := by omega
  have hne : a+1≠1 := by omega
  rw [if_neg hz,if_pos hle,if_neg hne]
  split_ifs <;> simp

theorem transferConstructionGraph_base_wrap (r : ℕ) (hr : 3 ≤ r) :
    (transferConstructionGraph r hr).Adj 1 r := by
  apply Or.inl
  simp only [transferPredecessors,show r≠0 by omega,ite_false,le_refl,ite_true,
    show r≠1 by omega,Finset.mem_insert,Finset.mem_singleton,true_or]

theorem transferConstructionGraph_row_endpoints (r i : ℕ) (hr : 3 ≤ r) :
    (transferConstructionGraph r hr).Adj 0 (transferRowStart r i) ∧
    (transferConstructionGraph r hr).Adj (i+1) (transferRowStart r i) ∧
    (transferConstructionGraph r hr).Adj 0 (transferRowStart r i+1) ∧
    (transferConstructionGraph r hr).Adj (i+1) (transferRowStart r i+1) := by
  have h0 := transferPredecessors_row_formula r i 0 hr (by omega)
  have h1 := transferPredecessors_row_formula r i 1 hr (by omega)
  simp only [Nat.add_zero,ite_true] at h0
  simp only [show (1:ℕ)≠0 by omega,ite_false,ite_true] at h1
  refine ⟨Or.inl ?_,Or.inl ?_,Or.inl ?_,Or.inl ?_⟩
  · rw [h0];simp
  · rw [h0];simp
  · rw [h1];split_ifs <;> simp
  · rw [h1];split_ifs <;> simp

theorem transferConstructionGraph_row_step (r i j : ℕ) (hr : 3 ≤ r)
    (hj : 0 < j) (hjr : j+1 < r) :
    (transferConstructionGraph r hr).Adj
      (transferRowStart r i+transferColumnOrder r j)
      (transferRowStart r i+transferColumnOrder r (j+1)) := by
  by_cases hj1 : j=1
  · subst j
    by_cases hr3 : r=3
    · subst r
      simp only [transferColumnOrder,ite_true,show (2:ℕ)≠1 by omega,ite_false,show 3-1=2 by omega]
      apply Or.inl
      rw [transferPredecessors_row_formula 3 i 1 (by omega) (by omega)]
      simp
    · have hr4 : 4≤r := by omega
      have h2 : 2≠r-1 := by omega
      simp only [transferColumnOrder,ite_true,show (2:ℕ)≠1 by omega,h2,ite_false,Nat.add_zero]
      apply Or.inl
      rw [transferPredecessors_row_formula r i 2 hr (by omega)]
      simp
  · by_cases hjlast : j+1=r-1
    · have hj2 : 2≤j := by omega
      have hjne : j≠r-1 := by omega
      simp only [transferColumnOrder,hj1,hjne,ite_false,hjlast,
        show r-1≠1 by omega,ite_true]
      apply Or.inr
      rw [transferPredecessors_row_formula r i j hr (by omega)]
      rw [if_neg (show j≠0 by omega),if_neg hj1,if_pos (show j=r-2 by omega)]
      exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
    · have hjne : j≠r-1 := by omega
      have hnext : j+1≠1 := by omega
      simp only [transferColumnOrder,hj1,hjne,hnext,hjlast,ite_false]
      apply Or.inl
      rw [transferPredecessors_row_formula r i (j+1) hr (by omega)]
      simp only [show j+1≠0 by omega,hnext,ite_false,show j+1≠2 by omega]
      apply Finset.mem_union_left
      simp only [Finset.mem_singleton]
      omega

end Oberwolfach
