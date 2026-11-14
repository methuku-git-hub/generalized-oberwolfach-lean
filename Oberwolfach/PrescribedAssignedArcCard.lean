module

public import Oberwolfach.PrescribedBadEdgeAssignments

@[expose] public section
/-! Orienting an assigned physical edge does not change the number of
edges in its assigned class. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I V:Type} [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V]

theorem prescribed_assigned_arc_card (K:SimpleGraph V) (assign:Sym2 V→I) (orient:Sym2 V→V×V)
    (horient:∀e∈K.edgeFinset,prescribedArcPhysical (orient e)=e) (i:I):
    (prescribedAssignedArcs K assign orient i).card=(K.edgeFinset.filter (fun e=>assign e=i)).card := by
  unfold prescribedAssignedArcs
  apply Finset.card_image_of_injOn
  intro a ha b hb h
  have haK:a∈K.edgeFinset:=(Finset.mem_filter.mp ha).1
  have hbK:b∈K.edgeFinset:=(Finset.mem_filter.mp hb).1
  calc
    a=prescribedArcPhysical (orient a):=(horient a haK).symm
    _=prescribedArcPhysical (orient b):=congrArg prescribedArcPhysical h
    _=b:=horient b hbK
end Oberwolfach
