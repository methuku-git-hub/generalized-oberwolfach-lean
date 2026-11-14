module

public import Oberwolfach.RawIntervalReservedLabelHubRestricted
public import Oberwolfach.ExtendingListStability

@[expose] public section
/-! Fixed-domain unassigned counts supply the exact list-extension tests. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_interval_reserved_label_count_eq_inter_card
    {V U Γ Color:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    [Fintype Γ] [Fintype Color]
    (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Γ Color) (w:U) (j:Color) (A:Finset V):
    rawIntervalReservedLabelHubCountOn π d σ w j A=
      ((A∩Finset.univ.filter (fun x=>rawIntervalFamilyState π d σ (x,w)=some (Sum.inr j))).card:ℝ):=by
  classical
  have heq:A∩Finset.univ.filter (fun x=>rawIntervalFamilyState π d σ (x,w)=some (Sum.inr j))=
      A.filter (fun x=>rawIntervalFamilyState π d σ (x,w)=some (Sum.inr j)):=by
    ext x
    simp
  rw [heq]
  simp [rawIntervalReservedLabelHubCountOn,←Finset.sum_filter]

theorem raw_reserved_label_list_extending_from_counts
    {V U Γ Color:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    [Fintype Γ] [Fintype Color]
    (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Γ Color) (w:U) (j:Color)
    (D:V→V→Prop) (β:ℝ) (hβ:0≤β)
    (hsize:β*Fintype.card V≤rawIntervalReservedLabelHubCountOn π d σ w j Finset.univ)
    (hout:∀x,β*Fintype.card V≤rawIntervalReservedLabelHubCountOn π d σ w j (directedOutNeighbours D x))
    (hin:∀x,β*Fintype.card V≤rawIntervalReservedLabelHubCountOn π d σ w j (directedInNeighbours D x))
    (hcommon:∀x y,x≠y→β*Fintype.card V≤rawIntervalReservedLabelHubCountOn π d σ w j
      (directedOutNeighbours D x∩directedInNeighbours D y)):
    IsExtendingList D (Finset.univ.filter (fun x=>rawIntervalFamilyState π d σ (x,w)=some (Sum.inr j))) β:=by
  refine ⟨hβ,?_,?_,?_⟩
  · simpa only [raw_interval_reserved_label_count_eq_inter_card,Finset.univ_inter] using hsize
  · intro x
    exact ⟨by simpa only [raw_interval_reserved_label_count_eq_inter_card] using hout x,
      by simpa only [raw_interval_reserved_label_count_eq_inter_card] using hin x⟩
  · intro x y hxy
    simpa only [raw_interval_reserved_label_count_eq_inter_card] using hcommon x y hxy
end Oberwolfach
