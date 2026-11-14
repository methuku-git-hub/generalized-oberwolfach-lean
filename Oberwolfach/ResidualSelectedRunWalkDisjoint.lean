module

public import Oberwolfach.ResidualSelectedRunWalk

@[expose] public section
/-! Distinct maximal runs give vertex-disjoint selected subpaths. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem selected_run_walks_disjoint {F:SimpleGraph V} {u v:V} (p:F.Walk u v)
    (hp:p.IsPath) (c d:ℕ) (hc:0<c) (hlen:p.length=c*d+4)
    (T:Finset ℕ) (hT:T⊆Finset.range d)
    (a b a' b':ℕ) (hr:(a,b)∈selectedSegmentRuns d T)
    (hr':(a',b')∈selectedSegmentRuns d T) (hne:(a,b)≠(a',b')):
    Disjoint (selectedRunWalk p c a b ((selected_run_mem d T hT a b).mp hr).1).support.toFinset
      (selectedRunWalk p c a' b' ((selected_run_mem d T hT a' b').mp hr').1).support.toFinset := by
  have hh: IsSelectedSegmentRun T a b := (selected_run_mem d T hT a b).mp hr
  have hh': IsSelectedSegmentRun T a' b' := (selected_run_mem d T hT a' b').mp hr'
  have hab:=hh.1
  have ha'b':=hh'.1
  have hbT:b∈T:=hh.2.1 b hh.1 le_rfl
  have hb'T:b'∈T:=hh'.2.1 b' hh'.1 le_rfl
  have hb:b<d:=by have z:=hT hbT;simpa using z
  have hb':b'<d:=by have z:=hT hb'T;simpa using z
  have ha:2+c*a≤2+c*(b+1) := by
    have z:=Nat.mul_le_mul_left c (show a≤b+1 by omega)
    omega
  have ha':2+c*a'≤2+c*(b'+1) := by
    have z:=Nat.mul_le_mul_left c (show a'≤b'+1 by omega)
    omega
  have hright:2+c*(b+1)≤p.length := by
    have z:=Nat.mul_le_mul_left c (show b+1≤d by omega)
    rw [hlen];omega
  have hright':2+c*(b'+1)≤p.length := by
    have z:=Nat.mul_le_mul_left c (show b'+1≤d by omega)
    rw [hlen];omega
  rcases distinct_selected_runs_separated d T hT a b a' b' hr hr' hne with h|h
  · have hsep:2+c*(b+1)<2+c*a' := by
      have z:=Nat.mul_lt_mul_of_pos_left h hc
      omega
    exact disjoint_path_intervals p hp _ _ _ _ ha ha' hright' hsep
  · have hsep:2+c*(b'+1)<2+c*a := by
      have z:=Nat.mul_lt_mul_of_pos_left h hc
      omega
    exact (disjoint_path_intervals p hp _ _ _ _ ha' ha hright hsep).symm
end Oberwolfach
