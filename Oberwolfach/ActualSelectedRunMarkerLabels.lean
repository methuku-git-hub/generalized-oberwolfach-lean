module

public import Oberwolfach.ActualSelectedRunUniqueMarker
public import Oberwolfach.DisjointOrbitLabelsInjective

@[expose] public section
/-! Every selected segment of every actual maximal run has a distinct
(parent, interval-position) pair and hence a distinct marked label. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X K J:Type} [Fintype X] [DecidableEq X] [DecidableEq K] [DecidableEq J] {G:SimpleGraph X}

def actualSelectedRunMarkerIndex (data:ActualResidualData (K:=K) (J:=J) G):Type:=
  Σr:SelectedRunIndex data.s₂ data.d data.T,
    {j:Fin (data.d+1) // r.2.val.1≤j.val ∧ j.val≤r.2.val.2+1}

instance (data:ActualResidualData (K:=K) (J:=J) G):Fintype (actualSelectedRunMarkerIndex data):=by
  classical
  unfold actualSelectedRunMarkerIndex
  infer_instance

def actualSelectedRunMarkerParentPosition (data:ActualResidualData (K:=K) (J:=J) G):
    actualSelectedRunMarkerIndex data→K×Fin (data.d+1):=fun z=>(z.1.1.val,z.2.val)

theorem actual_selected_run_marker_parent_position_injective
    (data:ActualResidualData (K:=K) (J:=J) G):
    Function.Injective (actualSelectedRunMarkerParentPosition data):=by
  rintro ⟨r,⟨j,hj⟩⟩ ⟨s,⟨k,hk⟩⟩ he
  change (r.1.val,j)=(s.1.val,k) at he
  have hp:r.1.val=s.1.val:=congrArg Prod.fst he
  have hjk:j=k:=congrArg Prod.snd he
  have hr:r=s:=actual_selected_run_unique_at_marker data r s j.val hp hj.1 hj.2
    (by simpa only [←hjk] using hk.1) (by simpa only [←hjk] using hk.2)
  subst s
  subst k
  rfl

theorem actual_selected_run_marker_labels_injective
    {V:Type} [Fintype V] [DecidableEq V] (data:ActualResidualData (K:=K) (J:=J) G)
    (π:Equiv.Perm V) (root:K→V)
    (hinj:∀i,Function.Injective (fun j:Fin (data.d+1)=>(π^j.val) (root i)))
    (hdis:∀i j,i≠j→Disjoint (permutationWindow π 0 data.d (root i)) (permutationWindow π 0 data.d (root j))):
    Function.Injective (fun z:actualSelectedRunMarkerIndex data=>(π^z.2.val.val) (root z.1.1.val)):=by
  have ho:=disjoint_extended_orbit_labels_injective π data.d root hinj hdis
  intro a b he
  apply actual_selected_run_marker_parent_position_injective data
  apply ho
  exact he
end Oberwolfach

namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_selected_run_bounds
    {X K J:Type} [Fintype X] [DecidableEq X] [DecidableEq K] [DecidableEq J]
    {G:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) G)
    (r:SelectedRunIndex data.s₂ data.d data.T):r.2.val.1≤r.2.val.2 ∧ r.2.val.2<data.d:=by
  have hr:=(selected_run_mem data.d (data.T r.1.val) (data.hT r.1.val) r.2.val.1 r.2.val.2).mp r.2.property
  have hh:=data.hT r.1.val (hr.2.1 r.2.val.2 hr.1 le_rfl)
  exact ⟨hr.1,Finset.mem_range.mp hh⟩

theorem actual_distinct_run_markers_have_distinct_labels
    {X V K J:Type} [Fintype X] [DecidableEq X] [Fintype V] [DecidableEq V] [DecidableEq K] [DecidableEq J]
    {G:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) G)
    (π:Equiv.Perm V) (root:K→V)
    (hinj:∀i,Function.Injective (fun j:Fin (data.d+1)=>(π^j.val) (root i)))
    (hdis:∀i j,i≠j→Disjoint (permutationWindow π 0 data.d (root i)) (permutationWindow π 0 data.d (root j)))
    (r s:SelectedRunIndex data.s₂ data.d data.T) (hne:r≠s)
    (j k:Fin (data.d+1))
    (hj:r.2.val.1≤j.val ∧ j.val≤r.2.val.2+1)
    (hk:s.2.val.1≤k.val ∧ k.val≤s.2.val.2+1):
    (π^j.val) (root r.1.val)≠(π^k.val) (root s.1.val):=by
  intro he
  have hh:(⟨r,⟨j,hj⟩⟩:actualSelectedRunMarkerIndex data)=⟨s,⟨k,hk⟩⟩:=
    (actual_selected_run_marker_labels_injective data π root hinj hdis) he
  exact hne (congrArg Sigma.fst hh)
end Oberwolfach
