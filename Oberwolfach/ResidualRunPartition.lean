module

public import Oberwolfach.ResidualRunFamilyCounts

@[expose] public section
/-! Maximal selected runs partition the selected segment indices. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem selected_runs_with_common_segment_equal (T:Finset ℕ)
    (a b a' b' j:ℕ) (h:IsSelectedSegmentRun T a b)
    (h':IsSelectedSegmentRun T a' b')
    (haj:a≤j) (hjb:j≤b) (ha'j:a'≤j) (hjb':j≤b'):
    a=a' ∧ b=b' := by
  have hab:=h.1
  have ha'b':=h'.1
  have haa:a=a' := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt|hgt
    · have hp:a'-1∈T := h.2.1 (a'-1) (by omega) (by omega)
      rcases h'.2.2.1 with hzero|hnot
      · omega
      · exact hnot hp
    · have hp:a-1∈T := h'.2.1 (a-1) (by omega) (by omega)
      rcases h.2.2.1 with hzero|hnot
      · omega
      · exact hnot hp
  subst a'
  exact ⟨rfl,selected_run_end_unique T a b b' h h'⟩

theorem selected_run_intervals_partition (d:ℕ) (T:Finset ℕ)
    (hT:T⊆Finset.range d):
    (selectedSegmentRuns d T).biUnion (fun p=>Finset.Icc p.1 p.2)=T ∧
    (↑(selectedSegmentRuns d T):Set (ℕ×ℕ)).PairwiseDisjoint
      (fun p=>Finset.Icc p.1 p.2) := by
  constructor
  · ext j
    constructor
    · intro hj
      obtain ⟨p,hp,hj⟩:=Finset.mem_biUnion.mp hj
      have hr: IsSelectedSegmentRun T p.1 p.2 := (selected_run_mem d T hT p.1 p.2).mp (by simpa using hp)
      exact hr.2.1 j (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2
    · intro hj
      obtain ⟨a,b,hab,haj,hjb⟩:=selected_segment_in_maximal_run d T hT j hj
      exact Finset.mem_biUnion.mpr ⟨(a,b),hab,Finset.mem_Icc.mpr ⟨haj,hjb⟩⟩
  · intro p hp q hq hpq
    apply Finset.disjoint_left.mpr
    intro j hj hj'
    rcases p with ⟨a,b⟩
    rcases q with ⟨a',b'⟩
    have he:=selected_runs_with_common_segment_equal T a b a' b' j
      ((selected_run_mem d T hT a b).mp hp) ((selected_run_mem d T hT a' b').mp hq)
      (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2
      (Finset.mem_Icc.mp hj').1 (Finset.mem_Icc.mp hj').2
    exact hpq (by simp [he.1,he.2])
end Oberwolfach
