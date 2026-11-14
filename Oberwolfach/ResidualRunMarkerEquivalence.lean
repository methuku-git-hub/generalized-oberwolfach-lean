module

public import Oberwolfach.ResidualRunContainingSegment

@[expose] public section
/-! A marker is deleted precisely when it lies inside a selected run. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem adjacent_selected_segments_iff_run_interior (d:ℕ) (T:Finset ℕ)
    (hT:T⊆Finset.range d) (j:ℕ):
    (0<j ∧ j∈T ∧ j-1∈T) ↔
      ∃ a b,(a,b)∈selectedSegmentRuns d T ∧ a<j ∧ j≤b := by
  constructor
  · rintro ⟨hj0,hj,hprev⟩
    obtain ⟨a,b,hab,haj,hjb⟩:=selected_segment_in_maximal_run d T hT j hj
    have hr: IsSelectedSegmentRun T a b := (selected_run_mem d T hT a b).mp hab
    have haj':a<j := by
      by_contra h
      have haeq:a=j := by omega
      subst a
      rcases hr.2.2.1 with h0|hnot
      · omega
      · exact hnot hprev
    exact ⟨a,b,hab,haj',hjb⟩
  · rintro ⟨a,b,hab,haj,hjb⟩
    have hr: IsSelectedSegmentRun T a b := (selected_run_mem d T hT a b).mp hab
    refine ⟨by omega,hr.2.1 j (by omega) hjb,?_⟩
    exact hr.2.1 (j-1) (by omega) (by omega)

theorem surviving_segment_marker_iff_avoids_runs (d:ℕ) (T:Finset ℕ)
    (hT:T⊆Finset.range d) (j:ℕ):
    j∈survivingSegmentMarkers d T ↔
      j≤d ∧ ∀ a b,(a,b)∈selectedSegmentRuns d T → ¬(a<j ∧ j≤b) := by
  simp only [survivingSegmentMarkers,Finset.mem_sdiff,Finset.mem_range,Finset.mem_filter]
  have heq:=adjacent_selected_segments_iff_run_interior d T hT j
  constructor
  · rintro ⟨hj,hn⟩
    refine ⟨by omega,?_⟩
    intro a b hab hmid
    have hh:=heq.mpr ⟨a,b,hab,hmid.1,hmid.2⟩
    exact hn ⟨hh.2.1,hh.1,hh.2.2⟩
  · rintro ⟨hj,hn⟩
    refine ⟨by omega,?_⟩
    rintro ⟨hjT,hj0,hprev⟩
    obtain ⟨a,b,hab,haj,hjb⟩:=heq.mp ⟨hj0,hjT,hprev⟩
    exact hn a b hab ⟨haj,hjb⟩
end Oberwolfach
