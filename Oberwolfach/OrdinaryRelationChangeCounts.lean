module

public import Oberwolfach.OrdinarySampleEditDegrees

@[expose] public section
/-! Symmetric differences of finite relation rows count precisely the
coordinates on which their truth values change. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_relation_change_sum {A:Type} [Fintype A] [DecidableEq A] (P Q:A→Prop):
    (∑a,if ¬(P a↔Q a) then (1:ℝ) else 0)=
      ((changed (Finset.univ.filter P) (Finset.univ.filter Q)).card:ℝ):=by
  have he:Finset.univ.filter (fun a=>¬(P a↔Q a))=
      changed (Finset.univ.filter P) (Finset.univ.filter Q):=by
    ext a
    simp only [changed,Finset.mem_union,Finset.mem_sdiff,Finset.mem_filter,Finset.mem_univ,true_and]
    tauto
  have hs:((Finset.univ.filter (fun a=>¬(P a↔Q a))).card:ℝ)=
      ∑a,if ¬(P a↔Q a) then (1:ℝ) else 0:=by
    simp only [Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  have hc:=congrArg Finset.card he
  have hc':=((Nat.cast_inj (R:=ℝ)).mpr hc)
  exact hs.symm.trans hc'
end Oberwolfach
