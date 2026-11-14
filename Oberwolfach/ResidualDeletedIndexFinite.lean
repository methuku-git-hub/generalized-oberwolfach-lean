module

public import Oberwolfach.ResidualDeletedPathsDisjoint

@[expose] public section
/-! The indexed family of selected runs and final paths is finite. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I:Type} [DecidableEq I]

instance selectedRunIndexFintype (s₂:Finset I) (d:ℕ) (T:I→Finset ℕ):
    Fintype (SelectedRunIndex s₂ d T) := by
  unfold SelectedRunIndex
  letI : ∀ i : {i // i∈s₂}, Fintype {r : ℕ×ℕ // r∈selectedSegmentRuns d (T i.1)} :=
    fun i=>Finset.Subtype.fintype (selectedSegmentRuns d (T i.1))
  infer_instance

instance deletedPathIndexFintype (s₁ s₂:Finset I) (d:ℕ) (T:I→Finset ℕ):
    Fintype (DeletedPathIndex s₁ s₂ d T) := by
  unfold DeletedPathIndex
  infer_instance

theorem selected_run_index_card (s₂:Finset I) (d:ℕ) (T:I→Finset ℕ):
    Fintype.card (SelectedRunIndex s₂ d T)=∑ i∈s₂,(selectedSegmentRuns d (T i)).card := by
  unfold SelectedRunIndex
  rw [Fintype.card_sigma]
  simp only [Fintype.card_coe]
  exact Finset.sum_attach s₂ (fun i=>(selectedSegmentRuns d (T i)).card)

theorem deleted_path_index_card (s₁ s₂:Finset I) (d:ℕ) (T:I→Finset ℕ):
    Fintype.card (DeletedPathIndex s₁ s₂ d T)=s₁.card+∑i∈s₂,(selectedSegmentRuns d (T i)).card := by
  unfold DeletedPathIndex
  rw [Fintype.card_sum,Fintype.card_coe,selected_run_index_card]
end Oberwolfach
