module

public import Oberwolfach.ResidualMaximalRunCounts

@[expose] public section
/-! Sum the maximal-run and surviving-marker counts over a path family. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {I:Type} [DecidableEq I]

theorem maximal_run_family_counts (s:Finset I) (d:ℕ) (hd:0<d)
    (T:I→Finset ℕ) (hT:∀ i∈s,T i⊆Finset.range d):
    let missing:=∑ i∈s,(d-(T i).card)
    let runs:=∑ i∈s,(selectedSegmentRuns d (T i)).card
    let markers:=∑ i∈s,(survivingSegmentMarkers d (T i)).card;
    markers=s.card+missing+runs ∧ runs≤s.card+missing ∧ s.card≤runs+missing ∧
    missing=d*s.card-∑ i∈s,(T i).card := by
  dsimp only
  have hmarker:∀i∈s,(survivingSegmentMarkers d (T i)).card=
      1+(d-(T i).card)+(selectedSegmentRuns d (T i)).card := by
    intro i hi
    exact (maximal_selected_runs_and_markers_count d hd (T i) (hT i hi)).1
  have hb1:∀i∈s,(selectedSegmentRuns d (T i)).card≤(d-(T i).card)+1 := by
    intro i hi
    exact (maximal_selected_runs_and_markers_count d hd (T i) (hT i hi)).2.1
  have hb2:∀i∈s,1≤(selectedSegmentRuns d (T i)).card+(d-(T i).card) := by
    intro i hi
    exact (maximal_selected_runs_and_markers_count d hd (T i) (hT i hi)).2.2.1
  have hsum1:=Finset.sum_le_sum hb1
  have hsum2:=Finset.sum_le_sum hb2
  have hsumM : (∑i∈s,(survivingSegmentMarkers d (T i)).card)=
      ∑i∈s,(1+(d-(T i).card)+(selectedSegmentRuns d (T i)).card) := by
    apply Finset.sum_congr rfl
    exact hmarker
  have hsub:∀i∈s,(T i).card≤d := by
    intro i hi
    have hh:=Finset.card_le_card (hT i hi)
    simpa using hh
  have hsumsub:=Finset.sum_tsub_distrib s hsub
  simp only [Finset.sum_add_distrib,Finset.sum_const_zero,Finset.sum_const,
    nsmul_eq_mul,Finset.card_attach, mul_comm] at hsum1 hsum2 hsumM hsumsub ⊢
  simp only [Nat.cast_id, mul_one] at hsum1 hsum2 hsumM hsumsub
  omega
end Oberwolfach
