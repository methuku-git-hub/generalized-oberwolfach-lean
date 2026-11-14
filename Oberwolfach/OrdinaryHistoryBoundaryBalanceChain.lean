module

public import Oberwolfach.OrdinaryWheelDeletionBoundaryBalanceChain
public import Oberwolfach.OrdinaryProtectedDeletionHistory

@[expose] public section
/-! Apply the boundary-discrepancy balance chain to the actual protected
physical deletion history. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_history_boundary_balance_chain
    (Q:SimpleGraph V) (H:V→U→Prop) (R:ℕ→SimpleGraph V) (S:ℕ→V→U→Prop)
    (I:Finset V) (J:Finset U) (r n:ℕ) (b:ℝ) (boundary:ℕ→ℝ)
    (hinit:∀v∈I,|((spanningRestriction Q I).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>H v u∧v∈I∧u∈J)).card|≤b)
    (hsub:∀i<n,R i≤ordinaryHistoryRim Q R S i ∧ ∀v u,S i v u→ ordinaryHistorySpokes H R S i v u)
    (hdec:∀i<n,HasOrdinaryWheelDecomposition (R i) (S i) r)
    (hboundary:∀i<n,∀v∈I,|(((R i)\spanningRestriction (R i) I).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>S i v u∧¬(v∈I∧u∈J))).card|≤boundary i):
    ∀v∈I,|((spanningRestriction (ordinaryHistoryRim Q R S n) I).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>ordinaryHistorySpokes H R S n v u∧v∈I∧u∈J)).card|≤b+∑j∈Finset.range n,boundary j :=by
  let Qs:=ordinaryHistoryRim Q R S
  let Hs:=ordinaryHistorySpokes H R S
  have hQ0:Qs 0=Q:=by
    ext x y
    simp [Qs,ordinaryHistoryRim,ordinaryDeletionHistory]
  have hH0:Hs 0=H:=by
    funext v u
    simp [Hs,ordinaryHistorySpokes,ordinarySpokesAfterPhysicalDeletion,ordinaryDeletionHistory]
  have hinit':∀v∈I,|((spanningRestriction (Qs 0) I).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>Hs 0 v u∧v∈I∧u∈J)).card|≤b:=by
    intro v hv
    rw [hQ0,hH0]
    convert hinit v hv using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hstep:∀i<n,Qs (i+1)=Qs i\R i ∧ Hs (i+1)=fun v u=>Hs i v u∧¬S i v u:=by
    intro i hi
    exact ⟨ordinary_history_rim_step Q R S i,ordinary_history_spokes_step H R S i⟩
  exact ordinary_wheel_deletion_boundary_balance_chain Qs R Hs S I J r n b boundary hinit' hstep hsub hdec hboundary n le_rfl
end Oberwolfach
