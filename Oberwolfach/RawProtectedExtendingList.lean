module

public import Oberwolfach.RawIntervalProtectedUnassignedList
public import Oberwolfach.ExtendingListStability

@[expose] public section
/-! Removing precisely the extended interval endpoints from an unassigned
list preserves its extending property with the actual interval-count loss. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_protected_unassigned_list_extends
    {V U Γ Color:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    [Fintype Γ] [DecidableEq Γ] [Fintype Color]
    (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Γ Color)
    (g₀ g₁:Γ) (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d σ g₀) t) (w:U)
    (D:V→V→Prop) (β lam:ℝ) (hlam:0≤lam)
    (hbudget:lam*Fintype.card V+(Fintype.card (retainedAndRawIntervalIndex π d σ g₀ g₁ t J w):ℝ)≤β*Fintype.card V)
    (hext:IsExtendingList D (Finset.univ.filter (fun x=>rawIntervalFamilyState π d σ (x,w)=none)) β):
    IsExtendingList D (rawIntervalProtectedUnassignedList π d σ g₀ g₁ t J w) lam:=by
  let L:=Finset.univ.filter (fun x=>rawIntervalFamilyState π d σ (x,w)=none)
  let L':=rawIntervalProtectedUnassignedList π d σ g₀ g₁ t J w
  apply extending_list_after_neighbourhood_changes D D L L' β lam 0
    (Fintype.card (retainedAndRawIntervalIndex π d σ g₀ g₁ t J w):ℝ) hlam (by norm_num) (by positivity) ?_ ?_ ?_ ?_ hext
  · exact_mod_cast raw_interval_protected_unassigned_loss π d σ g₀ g₁ t J w
  · intro x;simp
  · intro x;simp
  · simpa using hbudget
end Oberwolfach
