module

public import Oberwolfach.MarkedPaddingDegrees

@[expose] public section

/-! Padding uses fresh hub occurrences. An old hub keeps its original
spokes; each new hub has one marked spoke and exactly m ordinary spokes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {U S I:Type} [Fintype S] [Fintype I] [DecidableEq U] [DecidableEq I]

theorem padding_old_hub_count (hub:S→U) (js:S→Bool) (m:ℕ) (u:U) (j:Bool):
    Fintype.card {s // paddingSpokeHub (I:=I) hub m s=Sum.inl u∧paddingSpokeType js m s=j}=
      Fintype.card {s:S // hub s=u∧js s=j}:=by
  rw [finite_card_sum_predicate (fun s=>paddingSpokeHub (I:=I) hub m s=Sum.inl u∧paddingSpokeType js m s=j)]
  simp only [paddingSpokeHub,paddingSpokeType,Sum.elim_inl,Sum.elim_inr,Sum.inl.injEq,
    Sum.inr_ne_inl,false_and]
  simp only [Fintype.card_eq_zero,add_zero]

theorem padding_new_hub_count (hub:S→U) (js:S→Bool) (m:ℕ) (i:I) (j:Bool):
    Fintype.card {s // paddingSpokeHub hub m s=Sum.inr i∧paddingSpokeType js m s=j}=
      if j then 1 else m:=by
  rw [finite_card_sum_predicate (fun s=>paddingSpokeHub hub m s=Sum.inr i∧paddingSpokeType js m s=j)]
  simp only [paddingSpokeHub,paddingSpokeType,Sum.elim_inl,Sum.elim_inr,Sum.inl_ne_inr,
    Sum.inr.injEq,false_and,Fintype.card_eq_zero,zero_add]
  have he:Fintype.card {z:I×Fin (m+1) // z.1=i∧decide (z.2=0)=j}=
      Fintype.card {k:Fin (m+1) // decide (k=0)=j}:=by
    apply Fintype.card_congr
    exact {
      toFun:=fun z=>⟨z.val.2,z.property.2⟩
      invFun:=fun k=>⟨(i,k.val),rfl,k.property⟩
      left_inv:=fun z=>by apply Subtype.ext;exact Prod.ext z.property.1.symm rfl
      right_inv:=fun _=>rfl}
  rw [he]
  cases j
  · simp only [Bool.false_eq_true,ite_false,decide_eq_false_iff_not]
    rw [Fintype.card_subtype_compl,Fintype.card_subtype_eq,Fintype.card_fin]
    omega
  · simp only [ite_true,decide_eq_true_eq,Fintype.card_subtype_eq]

theorem padding_hub_balance (hub:S→U) (js:S→Bool) (m:ℕ)
    (hbal:∀ u,Fintype.card {s:S // hub s=u∧js s=false}=m*Fintype.card {s:S // hub s=u∧js s=true}):
    ∀ u:U⊕I,Fintype.card {s // paddingSpokeHub hub m s=u∧paddingSpokeType js m s=false}=
      m*Fintype.card {s // paddingSpokeHub hub m s=u∧paddingSpokeType js m s=true}:=by
  intro u
  cases u with
  | inl u=>simpa only [padding_old_hub_count] using hbal u
  | inr i=>simp only [padding_new_hub_count,Bool.false_eq_true,ite_false,ite_true,mul_one]

end Oberwolfach
