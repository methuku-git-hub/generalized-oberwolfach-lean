module

public import Oberwolfach.MarkedPathRestrictionCounts
public import Oberwolfach.MarkedHubFixedWeightRestriction
public import Oberwolfach.CommonMarkedCycleConstraintCounts

@[expose] public section

/-! Counts of cycles and common paths at a fixed hub after deletion of
rim occurrences. All spoke classes and both path roots stay fixed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype E] [Fintype K] [DecidableEq V]
    {tail head:E→V} {ktail khead:K→V} {m b:ℕ} {π:Equiv.Perm V} {H₀ Hₖ:V→U→Prop}

theorem hub_marked_cycle_rim_deletion_count (hm:1≤m) (PE:E→Prop) (PK:K→Prop) (u:U)
    (d:ℝ) (hd:0≤d)
    (hEout:∀ x,(∑ e,if ¬PE e∧tail e=x then (1:ℝ) else 0)≤d)
    (hKout:∀ x,(∑ e,if ¬PK e∧ktail e=x then (1:ℝ) else 0)≤d):
    (Fintype.card (HubMarkedCycle tail head ktail khead m π b H₀ Hₖ u):ℝ)-
      Fintype.card (HubMarkedCycle (fun e:{e // PE e}=>tail e.val) (fun e=>head e.val)
        (fun e:{e // PK e}=>ktail e.val) (fun e=>khead e.val) m π b H₀ Hₖ u)≤
      3*((m:ℝ)+1)*d*(Fintype.card V:ℝ)^m:=by
  rw [Fintype.card_congr (hubMarkedCycleCommonEquiv u),Fintype.card_congr (hubMarkedCycleCommonEquiv u)]
  exact commonMarkedCycle_deletion_count hm tail head ktail khead π b PE PK
    H₀ Hₖ H₀ Hₖ u u d hEout hKout (by intro u;simpa using hd) (by intro u;simpa using hd)

theorem hub_marked_path_rim_deletion_count (hm:1≤m) (PE:E→Prop) (PK:K→Prop)
    (u:U) (j:Bool) (v v':V) (d:ℝ) (hd:0≤d)
    (hEout:∀ x,(∑ e,if ¬PE e∧tail e=x then (1:ℝ) else 0)≤d)
    (hEin:∀ x,(∑ e,if ¬PE e∧head e=x then (1:ℝ) else 0)≤d)
    (hKout:∀ x,(∑ e,if ¬PK e∧ktail e=x then (1:ℝ) else 0)≤d)
    (hKin:∀ x,(∑ e,if ¬PK e∧khead e=x then (1:ℝ) else 0)≤d):
    (Fintype.card (RootFirstCommonMarkedPath tail head ktail khead m π b H₀ Hₖ j v v' u u):ℝ)-
      Fintype.card (RootFirstCommonMarkedPath (fun e:{e // PE e}=>tail e.val) (fun e=>head e.val)
        (fun e:{e // PK e}=>ktail e.val) (fun e=>khead e.val) m π b H₀ Hₖ j v v' u u)≤
      4*((m:ℝ)+1)*d*(Fintype.card V:ℝ)^(m-1):=
  rootFirstCommonMarkedPath_deletion_count hm PE PK H₀ Hₖ j v v' u u d
    hEout hEin hKout hKin (by intro u;simpa using hd) (by intro u;simpa using hd)

end Oberwolfach
