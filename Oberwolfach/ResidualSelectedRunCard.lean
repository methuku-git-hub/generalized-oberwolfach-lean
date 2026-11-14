module

public import Oberwolfach.ResidualSelectedRuns

@[expose] public section
/-! The starts are in bijection with maximal consecutive selected runs. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def selectedSegmentRuns (d:ℕ) (T:Finset ℕ):Finset (ℕ×ℕ) :=
  ((Finset.range d).product (Finset.range d)).filter (fun p=>IsSelectedSegmentRun T p.1 p.2)

theorem selected_run_mem (d:ℕ) (T:Finset ℕ) (hT:T⊆Finset.range d) (a b:ℕ):
    (a,b)∈selectedSegmentRuns d T ↔ IsSelectedSegmentRun T a b := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    have hbT:b∈T:=h.2.1 b h.1 le_rfl
    have hbd:b<d := by have hh:=hT hbT;simpa using hh
    have hab:=h.1
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),Finset.mem_range.mpr hbd⟩,h⟩

theorem selected_segment_runs_card (d:ℕ) (T:Finset ℕ)
    (hT:T⊆Finset.range d):
    (selectedSegmentRuns d T).card=(selectedRunStarts T).card := by
  apply Finset.card_bij (fun p _=>p.1)
  · intro p hp
    exact selected_run_start_of_run T p.1 p.2 ((selected_run_mem d T hT p.1 p.2).mp (by simpa using hp))
  · intro p hp q hq heq
    rcases p with ⟨a,b⟩
    rcases q with ⟨a',b'⟩
    simp only at heq
    subst a'
    have hb:=selected_run_end_unique T a b b' ((selected_run_mem d T hT a b).mp hp)
      ((selected_run_mem d T hT a b').mp hq)
    simp [hb]
  · intro a ha
    obtain ⟨b,hb,_⟩:=selected_run_exists_unique_from_start d T hT a ha
    exact ⟨(a,b),(selected_run_mem d T hT a b).mpr hb,rfl⟩
end Oberwolfach
