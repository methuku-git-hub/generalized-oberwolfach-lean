module

public import Oberwolfach.ResidualActualData

@[expose] public section
/-! Any relation on successive vertices of a buffered parent walk is inherited
by each of its actual selected runs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem walk_interval_inherits_successor_relation
    {X:Type} [Fintype X] [DecidableEq X] {G:SimpleGraph X} {u v:X} (p:G.Walk u v)
    (a b:ℕ) (hab:a≤b) (hb:b≤p.length) (R:X→X→Prop)
    (hp:∀j<p.length,R (p.getVert j) (p.getVert (j+1))):
    ∀j<(walkInterval p a b hab).length,
      R ((walkInterval p a b hab).getVert j) ((walkInterval p a b hab).getVert (j+1)):=by
  intro j hj
  rw [walk_interval_length p a b hab hb] at hj
  rw [walk_interval_getVert p a b hab j (by omega),walk_interval_getVert p a b hab (j+1) (by omega)]
  simpa only [Nat.add_assoc] using hp (a+j) (by omega)

theorem actual_selected_run_inherits_parent_relation
    {X K J:Type} [Fintype X] [DecidableEq X] [DecidableEq K] [DecidableEq J]
    {G:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) G) (R:X→X→Prop)
    (hparent:∀i∈data.s₂,∀k<(data.P i).length,R ((data.P i).getVert k) ((data.P i).getVert (k+1))):
    ∀r:SelectedRunIndex data.s₂ data.d data.T,∀k<(data.path (.inr r)).length,
      R ((data.path (.inr r)).getVert k) ((data.path (.inr r)).getVert (k+1)):=by
  intro r
  rcases r with ⟨i,r⟩
  have hr:=(selected_run_mem data.d (data.T i.val) (data.hT i.val) r.val.1 r.val.2).mp r.property
  have hrbound:r.val.2<data.d := by
    have hh:=data.hT i.val (hr.2.1 r.val.2 hr.1 le_rfl)
    simpa using hh
  have hright:2+data.c*(r.val.2+1)≤(data.P i.val).length:=by
    rw [data.hlen i.val (Finset.mem_union_right _ i.property)]
    have hm:=Nat.mul_le_mul_left data.c (show r.val.2+1≤data.d by omega)
    omega
  change ∀k<(selectedRunWalk (data.P i.val) data.c r.val.1 r.val.2 hr.1).length,
    R ((selectedRunWalk (data.P i.val) data.c r.val.1 r.val.2 hr.1).getVert k)
      ((selectedRunWalk (data.P i.val) data.c r.val.1 r.val.2 hr.1).getVert (k+1))
  unfold selectedRunWalk
  exact walk_interval_inherits_successor_relation (data.P i.val) _ _ _ hright R (hparent i.val i.property)
end Oberwolfach

namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_selected_run_inherits_selected_parent_relation
    {X K J:Type} [Fintype X] [DecidableEq X] [DecidableEq K] [DecidableEq J]
    {G:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) G) (R:X→X→Prop)
    (hparent:∀i∈data.s₂,∀r∈selectedSegmentRuns data.d (data.T i),∀k,
      2+data.c*r.1≤k→k<2+data.c*(r.2+1)→
      R ((data.P i).getVert k) ((data.P i).getVert (k+1))):
    ∀r:SelectedRunIndex data.s₂ data.d data.T,∀k<(data.path (.inr r)).length,
      R ((data.path (.inr r)).getVert k) ((data.path (.inr r)).getVert (k+1)):=by
  intro r
  rcases r with ⟨i,r⟩
  have hr:=(selected_run_mem data.d (data.T i.val) (data.hT i.val) r.val.1 r.val.2).mp r.property
  have hrbound:r.val.2<data.d := by
    have hh:=data.hT i.val (hr.2.1 r.val.2 hr.1 le_rfl)
    simpa using hh
  have hright:2+data.c*(r.val.2+1)≤(data.P i.val).length:=by
    rw [data.hlen i.val (Finset.mem_union_right _ i.property)]
    have hm:=Nat.mul_le_mul_left data.c (show r.val.2+1≤data.d by omega)
    omega
  change ∀k<(selectedRunWalk (data.P i.val) data.c r.val.1 r.val.2 hr.1).length,
    R ((selectedRunWalk (data.P i.val) data.c r.val.1 r.val.2 hr.1).getVert k)
      ((selectedRunWalk (data.P i.val) data.c r.val.1 r.val.2 hr.1).getVert (k+1))
  unfold selectedRunWalk
  intro k hk
  rw [walk_interval_length _ _ _ _ hright] at hk
  rw [walk_interval_getVert _ _ _ _ k (by omega),walk_interval_getVert _ _ _ _ (k+1) (by omega)]
  simpa only [Nat.add_assoc] using hparent i.val i.property r.val r.property (2+data.c*r.val.1+k) (by omega) (by omega)
end Oberwolfach
