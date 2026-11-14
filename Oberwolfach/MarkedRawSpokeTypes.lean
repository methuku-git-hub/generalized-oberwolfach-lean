module

public import Oberwolfach.MarkedWheelRawCoordinates

@[expose] public section

/-! Recover the prescribed spoke types in the unrotated cyclic order.
In a rim-wheel pair, the tail root has an ordinary spoke and the head
root has a marked spoke exactly when the original arc is marked. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V} {b:ℕ} {H₀ HK:V→U→Prop}

 theorem marked_wheel_raw_spoke_types {m:ℕ}
    (W:MarkedWheel tail head ktail khead m π b H₀ HK) (z:Fin (m+1)→V) (k:Fin (m+1))
    (hW:∀ i,W.1.val i=z (canonicalMarkedRotation k i)):
    HK (z (finRotate (m+1) k)) W.2.val∧
      ∀ i,i≠finRotate (m+1) k→H₀ (z i) W.2.val:=by
  constructor
  · simpa only [hW,canonicalMarkedRotation_zero] using W.2.property.1
  · intro i hi
    let a:Fin (m+1):=(canonicalMarkedRotation k).symm i
    have hai:canonicalMarkedRotation k a=i:=Equiv.apply_symm_apply _ _
    have ha:a≠0:=by
      intro he
      rw [he,canonicalMarkedRotation_zero] at hai
      exact hi hai.symm
    have ht:H₀ (W.1.val a) W.2.val:=by
      revert ha
      refine Fin.cases (fun h=>False.elim (h rfl)) (fun j _=>W.2.property.2 j) a
    simpa only [hW,hai] using ht

 theorem marked_rim_wheel_root_spoke_types (n:ℕ) (hn:2≤n)
    (W:MarkedWheel tail head ktail khead (n+2) π b H₀ HK)
    (v w:V) (p:Fin (n+1)→V) (j:Bool)
    (hW:∀ i,W.1.val i=Fin.cons (α:=fun _=>V) v (Fin.cons w p)
      (canonicalMarkedRotation (if j then 0 else 3) i)):
    H₀ v W.2.val∧(if j then HK w W.2.val else H₀ w W.2.val):=by
  have ht:=marked_wheel_raw_spoke_types W (Fin.cons v (Fin.cons w p)) (if j then 0 else 3) hW
  have hrot0:finRotate (n+3) (0:Fin (n+3))=(0:Fin (n+2)).succ:=finRotate_castSucc_eq_succ (n+2) 0
  have hrot3val:(finRotate (n+3) (3:Fin (n+3))).val=4:=by
    rw [finRotate_apply]
    change ((3%(n+3))+1)%(n+3)=4
    rw [Nat.mod_eq_of_lt (by omega : 3<n+3),Nat.mod_eq_of_lt (by omega : 3+1<n+3)]
  have hzero3:(0:Fin (n+3))≠finRotate (n+3) 3:=by
    intro he;have hh:=congrArg Fin.val he;simp only [Fin.val_zero,hrot3val] at hh;omega
  have hone3:(0:Fin (n+2)).succ≠finRotate (n+3) 3:=by
    intro he;have hh:=congrArg Fin.val he;simp only [Fin.val_succ,Fin.val_zero,hrot3val] at hh;omega
  cases j with
  | false=>
    simp only [Bool.false_eq_true,ite_false] at ht ⊢
    exact ⟨by simpa only [Fin.cons_zero] using ht.2 0 hzero3,
      by simpa only [Fin.cons_succ,Fin.cons_zero] using ht.2 (0:Fin (n+2)).succ hone3⟩
  | true=>
    simp only [ite_true] at ht ⊢
    have hz:(0:Fin (n+3))≠finRotate (n+3) 0:=by rw [hrot0];exact Ne.symm (Fin.succ_ne_zero _)
    exact ⟨by simpa only [Fin.cons_zero] using ht.2 0 hz,
      by simpa only [hrot0,Fin.cons_succ,Fin.cons_zero] using ht.1⟩

end Oberwolfach
