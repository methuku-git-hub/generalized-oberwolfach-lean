module

public import Oberwolfach.OrdinaryWheelFamilies
public import Oberwolfach.Neighbourhoods

@[expose] public section

/-! Exact symmetric-difference sizes for deletion of an actual wheel
family. These are realised losses, with no sampling-density multiplier. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Z:Type} [Fintype V] [Fintype U] [Fintype Z] [DecidableEq V] [DecidableEq U]
  {Q F:SimpleGraph V} {H:V→U→Prop} {r:ℕ}

theorem changed_sdiff_of_subset {A:Type*} (S T:Finset A) (h:T⊆S):changed S (S\T)=T:=by
  classical
  ext x
  simp only [changed,Finset.mem_union,Finset.mem_sdiff]
  constructor
  · tauto
  · intro hx;left;exact ⟨h hx,by tauto⟩

theorem wheel_family_rim_deletion_change (C:Z→OrdinaryWheel Q F H r) (v:V):
    (changed (Q.neighborFinset v) ((Q\wheelFamilyRim C).neighborFinset v)).card=(wheelFamilyRim C).degree v:=by
  have he:(Q\wheelFamilyRim C).neighborFinset v=Q.neighborFinset v\(wheelFamilyRim C).neighborFinset v:=by
    ext a;simp only [SimpleGraph.mem_neighborFinset,SimpleGraph.sdiff_adj,Finset.mem_sdiff]
  have hs:(wheelFamilyRim C).neighborFinset v⊆Q.neighborFinset v:=by
    intro a ha
    exact (Q.mem_neighborFinset v a).mpr ((wheelFamily_subhost C).1 (((wheelFamilyRim C).mem_neighborFinset v a).mp ha))
  rw [he,←SimpleGraph.card_neighborFinset_eq_degree]
  convert congrArg Finset.card (changed_sdiff_of_subset (Q.neighborFinset v) ((wheelFamilyRim C).neighborFinset v) hs) using 1 <;> congr!

theorem wheel_family_spoke_row_deletion_change (C:Z→OrdinaryWheel Q F H r) (v:V):
    (changed (Finset.univ.filter (H v))
      (Finset.univ.filter (fun a=>H v a∧¬wheelFamilySpokes C v a))).card=
      (Finset.univ.filter (wheelFamilySpokes C v)).card:=by
  have he:Finset.univ.filter (fun a=>H v a∧¬wheelFamilySpokes C v a)=
      Finset.univ.filter (H v)\Finset.univ.filter (wheelFamilySpokes C v):=by ext a;simp
  have hs:Finset.univ.filter (wheelFamilySpokes C v)⊆Finset.univ.filter (H v):=by
    intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(wheelFamily_subhost C).2 v a (Finset.mem_filter.mp ha).2⟩
  rw [he]
  convert congrArg Finset.card (changed_sdiff_of_subset (Finset.univ.filter (H v)) (Finset.univ.filter (wheelFamilySpokes C v)) hs) using 1 <;> congr!

theorem wheel_family_spoke_column_deletion_change (C:Z→OrdinaryWheel Q F H r) (a:U):
    (changed (Finset.univ.filter (fun v=>H v a))
      (Finset.univ.filter (fun v=>H v a∧¬wheelFamilySpokes C v a))).card=
      (Finset.univ.filter (fun v=>wheelFamilySpokes C v a)).card:=by
  have he:Finset.univ.filter (fun v=>H v a∧¬wheelFamilySpokes C v a)=
      Finset.univ.filter (fun v=>H v a)\Finset.univ.filter (fun v=>wheelFamilySpokes C v a):=by ext v;simp
  have hs:Finset.univ.filter (fun v=>wheelFamilySpokes C v a)⊆Finset.univ.filter (fun v=>H v a):=by
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(wheelFamily_subhost C).2 v a (Finset.mem_filter.mp hv).2⟩
  rw [he]
  convert congrArg Finset.card (changed_sdiff_of_subset (Finset.univ.filter (fun v=>H v a)) (Finset.univ.filter (fun v=>wheelFamilySpokes C v a)) hs) using 1 <;> congr!

end Oberwolfach
