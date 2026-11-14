module

public import Oberwolfach.ResidualRunMarkerEquivalence

@[expose] public section
/-! The marker formula and deviation bound for the actual maximal runs. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem maximal_selected_runs_and_markers_count (d:ℕ) (hd:0<d)
    (T:Finset ℕ) (hT:T⊆Finset.range d):
    (survivingSegmentMarkers d T).card = 1+(d-T.card)+(selectedSegmentRuns d T).card ∧
    (selectedSegmentRuns d T).card≤(d-T.card)+1 ∧
    1≤(selectedSegmentRuns d T).card+(d-T.card) ∧
    ∀ j,j∈survivingSegmentMarkers d T ↔
      j≤d ∧ ∀ a b,(a,b)∈selectedSegmentRuns d T → ¬(a<j ∧ j≤b) := by
  have hcard:=selected_segment_runs_card d T hT
  have hmarker:=selected_run_marker_count_exact d T hT
  have hbounds:=selected_run_count_deviation d hd T hT
  refine ⟨?_,?_,?_,?_⟩
  · rw [hcard];exact hmarker
  · rw [hcard];exact hbounds.1
  · rw [hcard];exact hbounds.2
  · exact surviving_segment_marker_iff_avoids_runs d T hT
end Oberwolfach
