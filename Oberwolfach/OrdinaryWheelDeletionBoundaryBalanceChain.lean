module

public import Oberwolfach.OrdinaryWheelDeletionBoundaryTransferAt

@[expose] public section
/-! Along a wheel-deletion chain, inner imbalance accumulates only the
cross-boundary discrepancies of the actual deleted wheel families. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_wheel_deletion_boundary_balance_chain
    (Q R:ℕ→SimpleGraph V) (H E:ℕ→V→U→Prop) (I:Finset V) (J:Finset U)
    (r n:ℕ) (b:ℝ) (boundary:ℕ→ℝ)
    (hinit:∀v∈I,|((spanningRestriction (Q 0) I).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>H 0 v u∧v∈I∧u∈J)).card|≤b)
    (hstep:∀i<n,Q (i+1)=Q i\R i ∧ H (i+1)=fun v u=>H i v u∧¬E i v u)
    (hsub:∀i<n,R i≤Q i ∧ ∀v u,E i v u→H i v u)
    (hdec:∀i<n,HasOrdinaryWheelDecomposition (R i) (E i) r)
    (hboundary:∀i<n,∀v∈I,|(((R i)\spanningRestriction (R i) I).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>E i v u∧¬(v∈I∧u∈J))).card|≤boundary i):
    ∀i≤n,∀v∈I,|((spanningRestriction (Q i) I).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>H i v u∧v∈I∧u∈J)).card|≤b+∑j∈Finset.range i,boundary j :=by
  intro i hi
  induction i with
  | zero =>
    intro v hv
    simpa using hinit v hv
  | succ i ih =>
    intro v hv
    have hlt:i<n:=by omega
    have hprev:=ih (by omega) v hv
    have hh:=ordinary_wheel_deletion_boundary_transfer_at (Q i) (R i) (H i) (E i) I J r
      (b+∑j∈Finset.range i,boundary j) (boundary i) v (hsub i hlt).1 (hsub i hlt).2
      (hdec i hlt) hprev (hboundary i hlt v hv)
    have hQ:Q (i+1)=Q i\R i:=(hstep i hlt).1
    have hH:H (i+1)=fun v u=>H i v u∧¬E i v u:=(hstep i hlt).2
    simp only [Finset.sum_range_succ,←add_assoc]
    rw [hQ,hH]
    simp only [and_assoc]
    convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
