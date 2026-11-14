module

public import Oberwolfach.ResidualActualData

@[expose] public section
/-! The j-th segment boundary of an actual selected run is the original
parent marker at the corresponding interval position. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_selected_run_marker_getVert
    {X K J:Type} [Fintype X] [DecidableEq X] [DecidableEq K] [DecidableEq J]
    {G:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) G)
    (r:SelectedRunIndex data.s₂ data.d data.T) (j:ℕ)
    (hj:j≤r.2.val.2+1-r.2.val.1):
    (data.path (.inr r)).getVert (data.c*j)=
      (data.P r.1.val).getVert (2+data.c*(r.2.val.1+j)):=by
  rcases r with ⟨i,r⟩
  change j≤r.val.2+1-r.val.1 at hj
  have hr:=(selected_run_mem data.d (data.T i.val) (data.hT i.val) r.val.1 r.val.2).mp r.property
  change (selectedRunWalk (data.P i.val) data.c r.val.1 r.val.2 hr.1).getVert (data.c*j)=
    (data.P i.val).getVert (2+data.c*(r.val.1+j))
  unfold selectedRunWalk
  have hj':data.c*j≤(2+data.c*(r.val.2+1))-(2+data.c*r.val.1):=by
    have hm:=Nat.mul_le_mul_left data.c hj
    rw [Nat.add_sub_add_left,←Nat.mul_sub_left_distrib]
    exact hm
  rw [walk_interval_getVert _ _ _ _ (data.c*j) hj']
  congr 1
  rw [Nat.mul_add]
  omega
end Oberwolfach
