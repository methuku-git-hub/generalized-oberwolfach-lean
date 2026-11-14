module

public import Oberwolfach.ActualSelectedRunUniquePosition
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

def actualSelectedSegmentIndex (data:ActualResidualData (K:=K) (J:=J) G):Type:=
  Σr:SelectedRunIndex data.s₂ data.d data.T,
    {j:Fin (data.d+1) // r.2.val.1≤j.val ∧ j.val≤r.2.val.2}

instance (data:ActualResidualData (K:=K) (J:=J) G):Fintype (actualSelectedSegmentIndex data):=by
  classical
  unfold actualSelectedSegmentIndex
  infer_instance

def actualSelectedSegmentParentPosition (data:ActualResidualData (K:=K) (J:=J) G):
    actualSelectedSegmentIndex data→K×Fin (data.d+1):=fun z=>(z.1.1.val,z.2.val)

theorem actual_selected_segment_parent_position_injective
    (data:ActualResidualData (K:=K) (J:=J) G):
    Function.Injective (actualSelectedSegmentParentPosition data):=by
  rintro ⟨r,⟨j,hj⟩⟩ ⟨s,⟨k,hk⟩⟩ he
  change (r.1.val,j)=(s.1.val,k) at he
  have hp:r.1.val=s.1.val:=congrArg Prod.fst he
  have hjk:j=k:=congrArg Prod.snd he
  have hr:r=s:=actual_selected_run_unique_at_position data r s j.val hp hj.1 hj.2
    (by simpa only [←hjk] using hk.1) (by simpa only [←hjk] using hk.2)
  subst s
  subst k
  rfl

theorem actual_selected_segment_labels_injective
    {V:Type} [Fintype V] [DecidableEq V] (data:ActualResidualData (K:=K) (J:=J) G)
    (π:Equiv.Perm V) (root:K→V)
    (hinj:∀i,Function.Injective (fun j:Fin (data.d+1)=>(π^j.val) (root i)))
    (hdis:∀i j,i≠j→Disjoint (permutationWindow π 0 data.d (root i)) (permutationWindow π 0 data.d (root j))):
    Function.Injective (fun z:actualSelectedSegmentIndex data=>(π^z.2.val.val) (root z.1.1.val)):=by
  have ho:=disjoint_extended_orbit_labels_injective π data.d root hinj hdis
  intro a b he
  apply actual_selected_segment_parent_position_injective data
  apply ho
  exact he
end Oberwolfach
