module

public import Oberwolfach.OrdinaryCrossBalanceDeletionTransferAt

@[expose] public section
/-! Cross-balance along a deletion chain accumulates the cross discrepancies
of the actual deleted pairs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_cross_balance_deletion_chain_on_parent
    (Q R:ℕ→SimpleGraph V) (H E:ℕ→V→U→Prop) (I Parent:Finset V) (J:Finset U)
    (n:ℕ) (b:ℝ) (cross:ℕ→ℝ)
    (hinit:∀v∈Parent,v∉I→|(((Q 0).neighborFinset v∩I).card:ℝ)-2*(J.filter (H 0 v)).card|≤b)
    (hstep:∀i<n,Q (i+1)=Q i\R i ∧ H (i+1)=fun v u=>H i v u∧¬E i v u)
    (hsub:∀i<n,R i≤Q i ∧ ∀v u,E i v u→H i v u)
    (hcross:∀i<n,∀v∈Parent,v∉I→|(((R i).neighborFinset v∩I).card:ℝ)-2*(J.filter (E i v)).card|≤cross i):
    ∀i≤n,∀v∈Parent,v∉I→|(((Q i).neighborFinset v∩I).card:ℝ)-2*(J.filter (H i v)).card|≤b+∑j∈Finset.range i,cross j :=by
  intro i hi
  induction i with
  | zero => intro v hmem hv;simpa using hinit v hmem hv
  | succ i ih =>
    intro v hmem hv
    have hlt:i<n:=by omega
    have hprev:=ih (by omega) v hmem hv
    have hh:=ordinary_cross_balance_deletion_transfer_at (Q i) (R i) (H i) (E i) I J v
      (b+∑j∈Finset.range i,cross j) (cross i) (hsub i hlt).1 (hsub i hlt).2 hprev (hcross i hlt v hmem hv)
    have hQ:Q (i+1)=Q i\R i:=(hstep i hlt).1
    have hH:H (i+1)=fun v u=>H i v u∧¬E i v u:=(hstep i hlt).2
    simp only [Finset.sum_range_succ,←add_assoc]
    rw [hQ,hH]
    convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
