module

public import Oberwolfach.OrdinaryProtectedDeletionHistoryEdit

@[expose] public section
/-! Appending the actual next deletion extends the same physical history. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_deletion_history_congr
    (R R':ℕ→SimpleGraph V) (S S':ℕ→V→U→Prop) (n:ℕ)
    (hR:∀j<n,R j=R' j) (hS:∀j<n,S j=S' j):
    ordinaryDeletionHistory R S n=ordinaryDeletionHistory R' S' n:=by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [ordinaryDeletionHistory,ordinaryDeletionHistory]
    rw [ih (by intro j hj;exact hR j (by omega)) (by intro j hj;exact hS j (by omega))]
    rw [hR n (by omega),hS n (by omega)]

theorem ordinary_deletion_history_update
    (R:ℕ→SimpleGraph V) (S:ℕ→V→U→Prop) (n:ℕ) (D:SimpleGraph V) (E:V→U→Prop):
    ordinaryDeletionHistory (Function.update R n D) (Function.update S n E) n=
      ordinaryDeletionHistory R S n:=by
  apply ordinary_deletion_history_congr
  · intro j hj
    simp [Function.update_of_ne (show j≠n by omega)]
  · intro j hj
    simp [Function.update_of_ne (show j≠n by omega)]

theorem ordinary_history_append_rim
    (Q:SimpleGraph V) (R:ℕ→SimpleGraph V) (S:ℕ→V→U→Prop) (n:ℕ) (D:SimpleGraph V) (E:V→U→Prop):
    ordinaryHistoryRim Q (Function.update R n D) (Function.update S n E) (n+1)=ordinaryHistoryRim Q R S n\D:=by
  rw [ordinary_history_rim_step]
  simp only [Function.update_self,ordinaryHistoryRim,ordinary_deletion_history_update]

theorem ordinary_history_append_spokes
    (H:V→U→Prop) (R:ℕ→SimpleGraph V) (S:ℕ→V→U→Prop) (n:ℕ) (D:SimpleGraph V) (E:V→U→Prop):
    ordinaryHistorySpokes H (Function.update R n D) (Function.update S n E) (n+1)=
      fun v u=>ordinaryHistorySpokes H R S n v u∧¬E v u:=by
  rw [ordinary_history_spokes_step]
  simp only [Function.update_self,ordinaryHistorySpokes,ordinary_deletion_history_update]
end Oberwolfach
