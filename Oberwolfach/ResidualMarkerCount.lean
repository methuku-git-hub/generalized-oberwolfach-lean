module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Range
public import Mathlib.Tactic

@[expose] public section
/-! Count markers surviving a selection of consecutive segments on a path. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def selectedRunStarts (T:Finset ℕ):Finset ℕ :=
  T \ T.filter (fun j=>0<j ∧ j-1∈T)

def survivingSegmentMarkers (d:ℕ) (T:Finset ℕ):Finset ℕ :=
  Finset.range (d+1) \ T.filter (fun j=>0<j ∧ j-1∈T)

theorem surviving_segment_marker_count (d:ℕ) (T:Finset ℕ)
    (hT:T⊆Finset.range d):
    (survivingSegmentMarkers d T).card + T.card =
      (d+1)+(selectedRunStarts T).card := by
  let A:=T.filter (fun j=>0<j ∧ j-1∈T)
  have hAT:A⊆T := by intro x hx;exact (Finset.mem_filter.mp hx).1
  have hAr:A⊆Finset.range (d+1) := by
    intro x hx
    have hh:=hT (hAT hx)
    simp only [Finset.mem_range] at hh ⊢
    omega
  have h1:=Finset.card_sdiff_add_card_eq_card hAT
  have h2:=Finset.card_sdiff_add_card_eq_card hAr
  simp only [Finset.card_range] at h2
  change (Finset.range (d+1) \ A).card+T.card=(d+1)+(T\A).card
  omega
end Oberwolfach
