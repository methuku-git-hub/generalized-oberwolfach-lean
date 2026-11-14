module

public import Oberwolfach.BalancedTransferAlgebra

@[expose] public section

/-! The all-pairs formula on an actual neighbourhood. Coordinates outside
the neighbourhood are zero, rather than being silently included as indices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem selected_pair_transfer_identity {U : Type*} [Fintype U] [DecidableEq U]
    (P : U → Prop) (z : U → ℝ)
    (hz : ∑ i : {u // P u},z i.val=0) (hout : ∀ u,¬P u → z u=0) (h : U) :
    (∑ i : {u // P u},∑ j : {u // P u},
      z i.val*((if h=i.val then (1:ℝ) else 0)-(if h=j.val then 1 else 0)))/
        (Fintype.card {u // P u}:ℝ)=z h := by
  by_cases hh : P h
  · let hP : {u // P u} := ⟨h,hh⟩
    have he := balanced_pair_transfer_identity (fun i : {u // P u} => z i.val) hz hP
    convert he using 1
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have hi : h=i.val ↔ hP=i := ⟨fun e => Subtype.ext e,fun e => congrArg Subtype.val e⟩
    have hj : h=j.val ↔ hP=j := ⟨fun e => Subtype.ext e,fun e => congrArg Subtype.val e⟩
    simp only [hi,hj]
  · rw [hout h hh]
    have hn (i : {u // P u}) : h≠i.val := by
      intro he
      exact hh (he ▸ i.property)
    simp only [hn,ite_false,sub_self,mul_zero,Finset.sum_const_zero,zero_div]

end Oberwolfach
