module

public import Oberwolfach.ResidualRunStartsBounds

@[expose] public section
/-! Exact surviving-marker and run-count formulas in the manuscript's notation. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem selected_run_count_deviation (d:ℕ) (hd:0<d) (T:Finset ℕ)
    (hT:T⊆Finset.range d):
    (selectedRunStarts T).card≤(d-T.card)+1 ∧
      1≤(selectedRunStarts T).card+(d-T.card) := by
  have h:=selected_run_start_bounds d hd T hT
  rw [Finset.card_sdiff_of_subset hT,Finset.card_range] at h
  exact h

theorem selected_run_marker_count_exact (d:ℕ) (T:Finset ℕ)
    (hT:T⊆Finset.range d):
    (survivingSegmentMarkers d T).card =
      1+(d-T.card)+(selectedRunStarts T).card := by
  have h:=surviving_segment_marker_count d T hT
  have hle:T.card≤d := by
    have hh:=Finset.card_le_card hT
    simpa using hh
  omega
end Oberwolfach
