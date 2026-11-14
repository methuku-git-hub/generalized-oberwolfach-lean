module

public import Oberwolfach.ResidualRunArithmetic

@[expose] public section
/-! Maximal selected runs and their unique starting indices. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def IsSelectedSegmentRun (T:Finset ℕ) (a b:ℕ):Prop :=
  a≤b ∧ (∀ j,a≤j→j≤b→j∈T) ∧ (a=0 ∨ a-1∉T) ∧ b+1∉T

theorem selected_run_start_of_run (T:Finset ℕ) (a b:ℕ)
    (h:IsSelectedSegmentRun T a b):a∈selectedRunStarts T := by
  exact (selected_run_start_mem T a).mpr ⟨h.2.1 a le_rfl h.1,h.2.2.1⟩

theorem selected_run_end_unique (T:Finset ℕ) (a b b':ℕ)
    (h:IsSelectedSegmentRun T a b) (h':IsSelectedSegmentRun T a b'):b=b' := by
  have hab:=h.1
  have hab':=h'.1
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt|hgt
  · exact h.2.2.2 (h'.2.1 (b+1) (by omega) (by omega))
  · exact h'.2.2.2 (h.2.1 (b'+1) (by omega) (by omega))

theorem selected_run_exists_unique_from_start (d:ℕ) (T:Finset ℕ)
    (hT:T⊆Finset.range d) (a:ℕ) (ha:a∈selectedRunStarts T):
    ∃! b,IsSelectedSegmentRun T a b := by
  have ha':= (selected_run_start_mem T a).mp ha
  have had:a<d := by have hh:=hT ha'.1;simpa using hh
  have hex:∃ k,a≤k ∧ k∉T := by
    refine ⟨d,by omega,?_⟩
    intro hd
    have hh:=hT hd
    simp at hh
  let k:=Nat.find hex
  have hk:=Nat.find_spec hex
  change a≤k ∧ k∉T at hk
  have hak:a<k := by
    by_contra h
    have : k=a := by omega
    apply hk.2
    rw [this]
    exact ha'.1
  let b:=k-1
  have hb:a≤b := by dsimp [b];omega
  have hbk:b+1=k := by dsimp [b];omega
  have hr:IsSelectedSegmentRun T a b := by
    refine ⟨hb,?_,ha'.2,?_⟩
    · intro j haj hjb
      by_contra hj
      have hjk:j<k := by omega
      exact (Nat.find_min hex hjk) ⟨haj,hj⟩
    · simpa [hbk] using hk.2
  refine ⟨b,hr,?_⟩
  intro b' hr'
  exact selected_run_end_unique T a b' b hr' hr
end Oberwolfach
