module

public import Oberwolfach.ResidualRunPartition

@[expose] public section
/-! Distinct maximal selected runs have at least one unselected segment between them. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem distinct_selected_runs_separated (d:ℕ) (T:Finset ℕ)
    (hT:T⊆Finset.range d) (a b a' b':ℕ)
    (h:(a,b)∈selectedSegmentRuns d T) (h':(a',b')∈selectedSegmentRuns d T)
    (hne:(a,b)≠(a',b')):
    b+1<a' ∨ b'+1<a := by
  have hr: IsSelectedSegmentRun T a b := (selected_run_mem d T hT a b).mp h
  have hr': IsSelectedSegmentRun T a' b' := (selected_run_mem d T hT a' b').mp h'
  have haa:a≠a' := by
    intro heq
    subst a'
    have hb:=selected_run_end_unique T a b b' hr hr'
    exact hne (by simp [hb])
  rcases lt_or_gt_of_ne haa with ha|ha
  · left
    have hba:b<a' := by
      by_contra hh
      have he:=selected_runs_with_common_segment_equal T a b a' b' a' hr hr'
        (by omega) (by omega) (by omega) hr'.1
      exact hne (by simp [he.1,he.2])
    have hgap:b+1≠a' := by
      intro heq
      have haT:=hr'.2.1 a' le_rfl hr'.1
      apply hr.2.2.2
      simpa [heq] using haT
    omega
  · right
    have hb'a:b'<a := by
      by_contra hh
      have he:=selected_runs_with_common_segment_equal T a b a' b' a hr hr'
        (by omega) hr.1 (by omega) (by omega)
      exact hne (by simp [he.1,he.2])
    have hgap:b'+1≠a := by
      intro heq
      have haT:=hr.2.1 a le_rfl hr.1
      apply hr'.2.2.2
      simpa [heq] using haT
    omega
end Oberwolfach
