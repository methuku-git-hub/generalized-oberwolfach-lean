module

public import Oberwolfach.ResidualRunLengths

@[expose] public section
/-! Count the internal vertices of all selected runs. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators

theorem selected_run_scaled_interior_sum (d c:ℕ) (hc:0<c) (T:Finset ℕ)
    (hT:T⊆Finset.range d):
    (∑ p∈selectedSegmentRuns d T,(c*(p.2+1-p.1)-1))=
      c*T.card-(selectedSegmentRuns d T).card := by
  have hle:∀ p∈selectedSegmentRuns d T,1≤c*(p.2+1-p.1) := by
    intro p hp
    have hr: IsSelectedSegmentRun T p.1 p.2 := (selected_run_mem d T hT p.1 p.2).mp (by simpa using hp)
    have hlen:1≤p.2+1-p.1 := by have hh:=hr.1;omega
    have hh:=Nat.mul_pos hc hlen
    omega
  have hs:=Finset.sum_tsub_distrib (selectedSegmentRuns d T) hle
  simp only [Finset.sum_const,nsmul_eq_mul,Nat.cast_id,mul_one] at hs
  rw [selected_run_scaled_lengths_sum d c T hT] at hs
  exact hs
end Oberwolfach
