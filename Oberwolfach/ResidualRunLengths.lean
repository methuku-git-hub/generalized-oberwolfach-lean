module

public import Oberwolfach.ResidualRunPartition

@[expose] public section
/-! The lengths of the maximal runs sum to the number of selected segments. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators

theorem selected_run_lengths_sum (d:ℕ) (T:Finset ℕ)
    (hT:T⊆Finset.range d):
    (∑ p∈selectedSegmentRuns d T,(p.2+1-p.1))=T.card := by
  have hp:=selected_run_intervals_partition d T hT
  have hc:=Finset.card_biUnion hp.2
  rw [hp.1] at hc
  simpa only [Nat.card_Icc] using hc.symm

theorem selected_run_scaled_lengths_sum (d c:ℕ) (T:Finset ℕ)
    (hT:T⊆Finset.range d):
    (∑ p∈selectedSegmentRuns d T,c*(p.2+1-p.1))=c*T.card := by
  rw [←Finset.mul_sum,selected_run_lengths_sum d T hT]
end Oberwolfach
