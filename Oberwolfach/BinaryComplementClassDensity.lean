module

public import Oberwolfach.LongBinaryPartitionParameters

@[expose] public section
/-! Aggregating all other nonempty classes preserves a positive lower bound,
with the one-class case handled exactly at density one. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem binary_complement_density_from_nonempty_classes
    {I:Type} [Fintype I] (ρ:I→ℝ) (r:ℝ) (hρ:∀i,0≤ρ i)
    (hsum:∑i,ρ i=1) (hsmall:∀i,ρ i=0 ∨ r≤ρ i) (i:I):
    ρ i=1 ∨ r≤1-ρ i := by
  have herase:(∑j∈Finset.univ.erase i,ρ j)=1-ρ i:=by
    have hh:=Finset.sum_erase_add Finset.univ ρ (Finset.mem_univ i)
    rw [hsum] at hh
    linarith
  by_cases h:∃j,j≠i ∧ 0<ρ j
  · obtain ⟨j,hji,hj⟩:=h
    have hjr:r≤ρ j:=by
      rcases hsmall j with hz|hr
      · linarith
      · exact hr
    have hjmem:j∈Finset.univ.erase i:=by simp [hji]
    have hjle:ρ j≤∑j∈Finset.univ.erase i,ρ j:=by
      exact Finset.single_le_sum (fun k _=>hρ k) hjmem
    right
    linarith
  · left
    have hz:∀j∈Finset.univ.erase i,ρ j=0:=by
      intro j hj
      have hji:j≠i:=(Finset.mem_erase.mp hj).1
      have hh:¬0<ρ j:=by intro hjpos;exact h ⟨j,hji,hjpos⟩
      linarith [hρ j]
    have hempty:(∑j∈Finset.univ.erase i,ρ j)=0:=Finset.sum_eq_zero hz
    linarith
end Oberwolfach
