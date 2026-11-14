module

public import Oberwolfach.ResidualSelectedRunCard

@[expose] public section
/-! Every selected segment lies in a maximal consecutive selected run. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem selected_segment_in_maximal_run (d:ℕ) (T:Finset ℕ)
    (hT:T⊆Finset.range d) (j:ℕ) (hj:j∈T):
    ∃ a b,(a,b)∈selectedSegmentRuns d T ∧ a≤j ∧ j≤b := by
  let good := (Finset.range (j+1)).filter (fun a=>∀ k,a≤k→k≤j→k∈T)
  have hgood:good.Nonempty := by
    refine ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),?_⟩⟩
    intro k h1 h2
    have : k=j := by omega
    simpa [this] using hj
  let a:=good.min' hgood
  have ha:=Finset.min'_mem good hgood
  have had:a≤j := by
    have hh: a<j+1 := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
    omega
  have hagood:∀k,a≤k→k≤j→k∈T := (Finset.mem_filter.mp ha).2
  have haT:a∈T := hagood a le_rfl had
  have hstart:a∈selectedRunStarts T := by
    apply (selected_run_start_mem T a).mpr
    refine ⟨haT,?_⟩
    by_cases ha0:a=0
    · exact Or.inl ha0
    · right
      intro hapred
      have hpGood:a-1∈good := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_range.mpr (by omega),?_⟩
        intro k hk hjk
        by_cases heq:k=a-1
        · simpa [heq] using hapred
        · exact hagood k (by omega) hjk
      have hm:=Finset.min'_le good (a-1) hpGood
      omega
  obtain ⟨b,hb,_⟩:=selected_run_exists_unique_from_start d T hT a hstart
  have hjb:j≤b := by
    by_contra h
    have hnext: b+1≤j := by omega
    have hnextT:=hagood (b+1) (by have hh:=hb.1;omega) hnext
    exact hb.2.2.2 hnextT
  exact ⟨a,b,(selected_run_mem d T hT a b).mpr hb,had,hjb⟩
end Oberwolfach
