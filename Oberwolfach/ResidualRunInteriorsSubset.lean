module

public import Oberwolfach.ResidualSelectedMarkerSurvival

@[expose] public section
/-! Every selected-run interior lies in its original extended path. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem selected_run_interiors_subset_extended_path {F:SimpleGraph V} {u v:V}
    (p:F.Walk u v) (c d:ℕ) (hlen:p.length=c*d+4)
    (T:Finset ℕ) (hT:T⊆Finset.range d):
    selectedRunInteriors p c d T hT ⊆ p.support.toFinset := by
  intro x hx
  obtain ⟨r,_,hx⟩:=Finset.mem_biUnion.mp hx
  rcases r with ⟨⟨a,b⟩,hab⟩
  have hr: IsSelectedSegmentRun T a b := (selected_run_mem d T hT a b).mp hab
  have hbT:b∈T:=hr.2.1 b hr.1 le_rfl
  have hbd:b<d:=by have hh:=hT hbT;simpa using hh
  have hidx:2+c*a≤2+c*(b+1) := by
    have hh:=Nat.mul_le_mul_left c (show a≤b+1 by have z:=hr.1;omega)
    omega
  have hright:2+c*(b+1)≤p.length := by
    have hh:=Nat.mul_le_mul_left c (show b+1≤d by omega)
    rw [hlen];omega
  have hx':x∈(selectedRunWalk p c a b hr.1).support :=
    List.mem_toFinset.mp (Finset.mem_sdiff.mp hx).1
  obtain ⟨j,_,_,hj⟩:=(walk_interval_mem_support_iff p _ _ hidx hright x).mp hx'
  rw [←hj]
  exact List.mem_toFinset.mpr (p.getVert_mem_support j)
end Oberwolfach
