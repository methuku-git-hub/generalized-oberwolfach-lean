module

public import Oberwolfach.MarkedFiniteBalanceValues
public import Oberwolfach.MarkedOutsideBalance

@[expose] public section

/-! The outside-balance identities are full identities. They give zero
full numerical balance at outside roots, without asserting zero balance
on a smaller opposite-endpoint domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]

theorem markedFiniteBalance_zero_outside
    (tail head:E→V) (ktail khead:K→V) (HK:V→U→Prop)
    (A:Finset (E⊕K)) (S:Finset (V×U)) (m:ℕ) (X:Finset V) (Z:Finset U)
    (h:MarkedOutsideBalance tail head ktail khead HK A S m X Z)
    (z:V⊕U) (hz:Sum.elim (fun v=>v∉X) (fun u=>u∉Z) z) (i:Fin 4):
    markedFiniteBalance tail head ktail khead HK A S m z i=0:=by
  cases z with
  | inl v=>
    have ho:=h.directed v hz
    have hi:=h.row v hz
    have hk:=h.marked v hz
    fin_cases i <;> simp only [markedFiniteBalance,Matrix.cons_val_zero',Matrix.cons_val_succ'] <;>
      simp only [←Set.ncard_coe_finset,Finset.coe_filter] at ho hi hk ⊢
    · rw [←ho,hi,sub_self]
    · rw [hi,sub_self]
    · rw [hk,sub_self]
  | inr u=>
    have hh:=h.hub u hz
    fin_cases i <;> simp only [markedFiniteBalance,Matrix.cons_val_zero',Matrix.cons_val_succ'] <;>
      simp only [←Set.ncard_coe_finset,Finset.coe_filter] at hh ⊢
    rw [hh,Nat.cast_mul,sub_self]

end Oberwolfach
