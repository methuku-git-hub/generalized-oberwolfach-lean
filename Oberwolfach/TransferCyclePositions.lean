module

public import Oberwolfach.TransferGreedyEdges

@[expose] public section

/-! Every cycle used by the signed transfer is contained in the explicit
ordered construction graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem cycleGraph_adj_natural_cases (r : ℕ) (hr : 3 ≤ r) (i j : Fin r)
    (h : (SimpleGraph.cycleGraph r).Adj i j) :
    (i:ℕ)+1=j ∨ (j:ℕ)+1=i ∨ ((i:ℕ)=0 ∧ (j:ℕ)=r-1) ∨ ((j:ℕ)=0 ∧ (i:ℕ)=r-1) := by
  have hi := i.isLt
  have hj := j.isLt
  rcases (cycleGraph_modular_adj (by omega) i j).mp h with h|h
  · by_cases hlt : (i:ℕ)+1 < r
    · rw [Nat.mod_eq_of_lt hlt] at h
      exact Or.inl h
    · have he : (i:ℕ)+1=r := by omega
      rw [he,Nat.mod_self] at h
      exact Or.inr (Or.inr (Or.inr ⟨h.symm,by omega⟩))
  · by_cases hlt : (j:ℕ)+1 < r
    · rw [Nat.mod_eq_of_lt hlt] at h
      exact Or.inr (Or.inl h)
    · have he : (j:ℕ)+1=r := by omega
      rw [he,Nat.mod_self] at h
      exact Or.inr (Or.inr (Or.inl ⟨h.symm,by omega⟩))

theorem transferConstructionGraph_base_cycle (r : ℕ) (hr : 3 ≤ r) (i j : Fin r)
    (h : (SimpleGraph.cycleGraph r).Adj i j) :
    (transferConstructionGraph r hr).Adj ((i:ℕ)+1) ((j:ℕ)+1) := by
  rcases cycleGraph_adj_natural_cases r hr i j h with h|h|⟨hi,hj⟩|⟨hj,hi⟩
  · rw [← h]
    exact transferConstructionGraph_base_step r ((i:ℕ)+1) hr (by omega) (by omega)
  · rw [← h]
    exact (transferConstructionGraph_base_step r ((j:ℕ)+1) hr (by omega) (by omega)).symm
  · have he : r-1+1=r := by omega
    simpa only [hi,hj,Nat.zero_add,he] using transferConstructionGraph_base_wrap r hr
  · have he : r-1+1=r := by omega
    simpa only [hi,hj,Nat.zero_add,he] using (transferConstructionGraph_base_wrap r hr).symm

def transferCyclePosition (r i a : ℕ) (j : Fin r) : ℕ :=
  if (j:ℕ)=0 then a else transferRowStart r i+transferColumnOrder r j

theorem transferCyclePosition_step (r i a : ℕ) (hr : 3 ≤ r) (ha : a=0 ∨ a=i+1)
    (j l : Fin r) (hj : (j:ℕ)+1=l) :
    (transferConstructionGraph r hr).Adj (transferCyclePosition r i a j) (transferCyclePosition r i a l) := by
  have hjr : (j:ℕ)+1 < r := by rw [hj];exact l.isLt
  by_cases hj0 : (j:ℕ)=0
  · have hl1 : (l:ℕ)=1 := by omega
    have hl0 : (l:ℕ)≠0 := by omega
    simp only [transferCyclePosition,hj0,ite_true,hl0,ite_false,hl1,transferColumnOrder,Nat.add_zero]
    rcases ha with rfl|rfl
    · exact (transferConstructionGraph_row_endpoints r i hr).1
    · exact (transferConstructionGraph_row_endpoints r i hr).2.1
  · have hl0 : (l:ℕ)≠0 := by omega
    simp only [transferCyclePosition,hj0,hl0,ite_false]
    rw [← hj]
    exact transferConstructionGraph_row_step r i j hr (by omega) hjr

theorem transferCyclePosition_wrap (r i a : ℕ) (hr : 3 ≤ r) (ha : a=0 ∨ a=i+1)
    (j l : Fin r) (hj : (j:ℕ)=0) (hl : (l:ℕ)=r-1) :
    (transferConstructionGraph r hr).Adj (transferCyclePosition r i a j) (transferCyclePosition r i a l) := by
  have hl0 : (l:ℕ)≠0 := by omega
  have hl1 : (l:ℕ)≠1 := by omega
  simp only [transferCyclePosition,hj,ite_true,hl0,ite_false,transferColumnOrder,hl1,hl,show r-1≠0 by omega,show r-1≠1 by omega,ite_false]
  rcases ha with rfl|rfl
  · exact (transferConstructionGraph_row_endpoints r i hr).2.2.1
  · exact (transferConstructionGraph_row_endpoints r i hr).2.2.2

theorem transferConstructionGraph_row_cycle (r i a : ℕ) (hr : 3 ≤ r) (ha : a=0 ∨ a=i+1)
    (j l : Fin r) (h : (SimpleGraph.cycleGraph r).Adj j l) :
    (transferConstructionGraph r hr).Adj (transferCyclePosition r i a j) (transferCyclePosition r i a l) := by
  rcases cycleGraph_adj_natural_cases r hr j l h with h|h|⟨hj,hl⟩|⟨hl,hj⟩
  · exact transferCyclePosition_step r i a hr ha j l h
  · exact (transferCyclePosition_step r i a hr ha l j h).symm
  · exact transferCyclePosition_wrap r i a hr ha j l hj hl
  · exact (transferCyclePosition_wrap r i a hr ha l j hl hj).symm

end Oberwolfach
