module

public import Oberwolfach.RawIntervalUnassignedHubRestricted
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

theorem raw_interval_unassigned_count_eq_inter_card
    {V U Γ Color:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    [Fintype Γ] [Fintype Color]
    (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Γ Color) (w:U) (A:Finset V):
    rawIntervalUnassignedHubCountOn π d σ w A=
      ((A∩Finset.univ.filter (fun x=>rawIntervalFamilyState π d σ (x,w)=none)).card:ℝ):=by
  classical
  have heq:A∩Finset.univ.filter (fun x=>rawIntervalFamilyState π d σ (x,w)=none)=
      A.filter (fun x=>rawIntervalFamilyState π d σ (x,w)=none):=by
    ext x
    simp
  rw [heq]
  simp [rawIntervalUnassignedHubCountOn,←Finset.sum_filter]

theorem raw_unassigned_list_extending_from_counts
    {V U Γ Color:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    [Fintype Γ] [Fintype Color]
    (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Γ Color) (w:U)
    (D:V→V→Prop) (β:ℝ) (hβ:0≤β)
    (hsize:β*Fintype.card V≤rawIntervalUnassignedHubCountOn π d σ w Finset.univ)
    (hout:∀x,β*Fintype.card V≤rawIntervalUnassignedHubCountOn π d σ w (directedOutNeighbours D x))
    (hin:∀x,β*Fintype.card V≤rawIntervalUnassignedHubCountOn π d σ w (directedInNeighbours D x))
    (hcommon:∀x y,x≠y→β*Fintype.card V≤rawIntervalUnassignedHubCountOn π d σ w
      (directedOutNeighbours D x∩directedInNeighbours D y)):
    IsExtendingList D (Finset.univ.filter (fun x=>rawIntervalFamilyState π d σ (x,w)=none)) β:=by
  refine ⟨hβ,?_,?_,?_⟩
  · simpa only [raw_interval_unassigned_count_eq_inter_card,Finset.univ_inter] using hsize
  · intro x
    exact ⟨by simpa only [raw_interval_unassigned_count_eq_inter_card] using hout x,
      by simpa only [raw_interval_unassigned_count_eq_inter_card] using hin x⟩
  · intro x y hxy
    simpa only [raw_interval_unassigned_count_eq_inter_card] using hcommon x y hxy
end Oberwolfach
