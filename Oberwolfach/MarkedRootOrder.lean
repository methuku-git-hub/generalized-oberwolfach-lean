module

public import Oberwolfach.OrderedMarkedCommonPaths
public import Mathlib.Logic.Equiv.Fin.Rotate

@[expose] public section

/-! The two root-first orders used in the manuscript. For an ordinary
root the unique marked arc is from the second to the third free label. -/
set_option autoImplicit false
namespace Oberwolfach

def markedRootOrder (m : ℕ) (j : Bool) : Equiv.Perm (Fin (m+1)) :=
  if j then Equiv.refl _ else Equiv.addRight (3:Fin (m+1))

theorem markedRootOrder_successor (m : ℕ) (j : Bool) (k : Fin (m+1)) :
    markedRootOrder m j (finRotate (m+1) k)=finRotate (m+1) (markedRootOrder m j k) := by
  cases j
  · change finRotate (m+1) k+3=finRotate (m+1) (k+3)
    simp only [finRotate_apply]
    abel
  · rfl

theorem markedRootOrder_type (m : ℕ) (hm : 3<m+1) (j : Bool) :
    markedPositionType ((markedRootOrder m j).symm 0)=j := by
  cases j
  · have hn : ((Equiv.addRight (3:Fin (m+1))).symm 0)≠0 := by
      intro he
      have hh := congrArg (Equiv.addRight (3:Fin (m+1))) he
      simp only [Equiv.apply_symm_apply] at hh
      change (0:Fin (m+1))=0+3 at hh
      rw [zero_add] at hh
      have hv := congrArg Fin.val hh
      change 0 = 3 % (m+1) at hv
      rw [Nat.mod_eq_of_lt hm] at hv
      omega
    simpa only [markedRootOrder,Bool.false_eq_true,ite_false,markedPositionType,decide_eq_false_iff_not] using hn
  · simp [markedRootOrder,markedPositionType]

theorem markedRootOrder_marked_head (m : ℕ) : markedRootOrder m false 0=(3:Fin (m+1)) := by
  change (0:Fin (m+1))+3=3
  exact zero_add _

theorem markedRootOrder_marked_tail (m : ℕ) : markedRootOrder m false (Fin.last m)=(2:Fin (m+1)) := by
  have hh := markedRootOrder_successor m false (Fin.last m)
  rw [finRotate_last,markedRootOrder_marked_head,finRotate_apply] at hh
  have he : (2:Fin (m+1))+1=3 := by
    apply Fin.ext
    change (2 % (m+1)+1 % (m+1)) % (m+1) = 3 % (m+1)
    rw [← Nat.add_mod]
  exact add_right_cancel (hh.symm.trans he.symm)

end Oberwolfach
