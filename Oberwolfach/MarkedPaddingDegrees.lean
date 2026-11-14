module

public import Oberwolfach.MarkedRowAssignmentTypes
public import Mathlib.Logic.Equiv.Fin.Rotate

@[expose] public section

/-! Degrees of the actual occurrence union of a typed graph and padding
wheels. The incoming marked occurrence is the closing arc of each wheel;
the marked spoke is at its head. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U A S I:Type} [Fintype A] [Fintype S] [Fintype I] [DecidableEq V]

def paddingRimTail (src:A→V) {m:ℕ} (C:I→Fin (m+1)→V):A⊕(I×Fin (m+1))→V:=
  Sum.elim src (fun z=>C z.1 z.2)
def paddingRimHead (dst:A→V) {m:ℕ} (C:I→Fin (m+1)→V):A⊕(I×Fin (m+1))→V:=
  Sum.elim dst (fun z=>C z.1 (finRotate (m+1) z.2))
def paddingRimType (jr:A→Bool) (m:ℕ):A⊕(I×Fin (m+1))→Bool:=
  Sum.elim jr (fun z=>decide (z.2=Fin.last m))
def paddingSpokeRow (row:S→V) {m:ℕ} (C:I→Fin (m+1)→V):S⊕(I×Fin (m+1))→V:=
  Sum.elim row (fun z=>C z.1 z.2)
def paddingSpokeType (js:S→Bool) (m:ℕ):S⊕(I×Fin (m+1))→Bool:=
  Sum.elim js (fun z=>decide (z.2=0))
def paddingSpokeHub (hub:S→U) (m:ℕ):S⊕(I×Fin (m+1))→U⊕I:=
  Sum.elim (fun s=>Sum.inl (hub s)) (fun z=>Sum.inr z.1)

theorem finite_card_sum_predicate {X Y:Type} [Fintype X] [Fintype Y] (P:X⊕Y→Prop) [Fintype {z // P z}] [Fintype {x:X // P (Sum.inl x)}]
    [Fintype {y:Y // P (Sum.inr y)}]:
    Fintype.card {z // P z}=Fintype.card {x // P (Sum.inl x)}+Fintype.card {y // P (Sum.inr y)}:=by
  rw [Fintype.card_congr (Equiv.subtypeSum (p:=P)),Fintype.card_sum]

theorem finite_card_marked_fiber {X:Type} [Fintype X] (f:X→V) (j:X→Bool) (v:V):
    (Finset.univ.filter (fun e:{e:X // f e=v}=>j e.val=true)).card=
      Fintype.card {e:X // f e=v∧j e=true}:=by
  rw [←Fintype.card_subtype]
  apply Fintype.card_congr
  exact {
    toFun:=fun e=>⟨e.val.val,e.val.property,e.property⟩
    invFun:=fun e=>⟨⟨e.val,e.property.1⟩,e.property.2⟩
    left_inv:=fun _=>rfl
    right_inv:=fun _=>rfl}

theorem padding_cycle_incoming_count (m:ℕ) (C:I→Fin (m+1)→V) (v:V):
    Fintype.card {z:I×Fin (m+1) // C z.1 (finRotate (m+1) z.2)=v}=
      Fintype.card {z:I×Fin (m+1) // C z.1 z.2=v}:=by
  apply Fintype.card_congr
  exact {
    toFun:=fun z=>⟨(z.val.1,finRotate (m+1) z.val.2),z.property⟩
    invFun:=fun z=>⟨(z.val.1,(finRotate (m+1)).symm z.val.2),by simpa only [Equiv.apply_symm_apply] using z.property⟩
    left_inv:=fun z=>by apply Subtype.ext;exact Prod.ext rfl (Equiv.symm_apply_apply _ _)
    right_inv:=fun z=>by apply Subtype.ext;exact Prod.ext rfl (Equiv.apply_symm_apply _ _)}

theorem padding_cycle_marked_incoming_count (m:ℕ) (C:I→Fin (m+1)→V) (v:V):
    Fintype.card {z:I×Fin (m+1) // C z.1 (finRotate (m+1) z.2)=v∧decide (z.2=Fin.last m)=true}=
      Fintype.card {i:I // C i 0=v}:=by
  apply Fintype.card_congr
  refine {
    toFun:=fun z=>⟨z.val.1,?_⟩
    invFun:=fun i=>⟨(i.val,Fin.last m),?_⟩
    left_inv:=?_
    right_inv:=?_}
  · have he:z.val.2=Fin.last m:=of_decide_eq_true z.property.2
    simpa only [he,finRotate_last] using z.property.1
  · simpa only [finRotate_last,decide_true,and_true] using i.property
  · intro z
    apply Subtype.ext
    exact Prod.ext rfl (of_decide_eq_true z.property.2).symm
  · intro i
    rfl

theorem padding_cycle_marked_spoke_count (m:ℕ) (C:I→Fin (m+1)→V) (v:V):
    Fintype.card {z:I×Fin (m+1) // C z.1 z.2=v∧decide (z.2=0)=true}=
      Fintype.card {i:I // C i 0=v}:=by
  apply Fintype.card_congr
  refine {
    toFun:=fun z=>⟨z.val.1,?_⟩
    invFun:=fun i=>⟨(i.val,0),?_⟩
    left_inv:=?_
    right_inv:=?_}
  · have he:z.val.2=0:=of_decide_eq_true z.property.2
    simpa only [he] using z.property.1
  · simpa only [decide_true,and_true] using i.property
  · intro z
    apply Subtype.ext
    exact Prod.ext rfl (of_decide_eq_true z.property.2).symm
  · intro i
    rfl

theorem padding_row_balance (src dst:A→V) (row:S→V) (jr:A→Bool) (js:S→Bool)
    (m:ℕ) (C:I→Fin (m+1)→V)
    (hbal:∀ v,Fintype.card {e:A // dst e=v}=Fintype.card {e:A // src e=v}∧
      Fintype.card {e:A // dst e=v}=Fintype.card {s:S // row s=v})
    (hmark:∀ v,(Finset.univ.filter (fun e:{e:A // dst e=v}=>jr e.val=true)).card=
      (Finset.univ.filter (fun s:{s:S // row s=v}=>js s.val=true)).card):
    (∀ v,Fintype.card {e // paddingRimHead dst C e=v}=Fintype.card {e // paddingRimTail src C e=v}∧
      Fintype.card {e // paddingRimHead dst C e=v}=Fintype.card {s // paddingSpokeRow row C s=v})∧
    ∀ v,(Finset.univ.filter (fun e:{e // paddingRimHead dst C e=v}=>paddingRimType jr m e.val=true)).card=
      (Finset.univ.filter (fun s:{s // paddingSpokeRow row C s=v}=>paddingSpokeType js m s.val=true)).card:=by
  constructor
  · intro v
    rw [finite_card_sum_predicate (fun e=>paddingRimHead dst C e=v),
      finite_card_sum_predicate (fun e=>paddingRimTail src C e=v),
      finite_card_sum_predicate (fun e=>paddingSpokeRow row C e=v)]
    simp only [paddingRimHead,paddingRimTail,paddingSpokeRow,Sum.elim_inl,Sum.elim_inr,padding_cycle_incoming_count]
    exact ⟨congrArg (fun n=>n+Fintype.card {z:I×Fin (m+1) // C z.1 z.2=v}) (hbal v).1,
      congrArg (fun n=>n+Fintype.card {z:I×Fin (m+1) // C z.1 z.2=v}) (hbal v).2⟩
  · intro v
    rw [finite_card_marked_fiber,finite_card_marked_fiber]
    rw [finite_card_sum_predicate (fun e=>paddingRimHead dst C e=v∧paddingRimType jr m e=true),
      finite_card_sum_predicate (fun e=>paddingSpokeRow row C e=v∧paddingSpokeType js m e=true)]
    simp only [paddingRimHead,paddingSpokeRow,paddingRimType,paddingSpokeType,
      Sum.elim_inl,Sum.elim_inr,padding_cycle_marked_incoming_count,padding_cycle_marked_spoke_count]
    have hh:=hmark v
    rw [finite_card_marked_fiber,finite_card_marked_fiber] at hh
    exact congrArg (fun n=>n+Fintype.card {i:I // C i 0=v}) hh

end Oberwolfach
