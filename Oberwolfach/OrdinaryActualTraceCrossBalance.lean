module

public import Oberwolfach.OrdinaryCrossBalanceDeletionChain
public import Oberwolfach.OrdinaryProtectedDeletionHistory

@[expose] public section
/-! Cross-balance transfer on the actual host and the same physical history. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_actual_trace_cross_balance
    (Q G:SimpleGraph V) (H Hs:V→U→Prop) (R:ℕ→SimpleGraph V) (S:ℕ→V→U→Prop)
    (A:Finset (Sym2 V⊕(V×U))) (I:Finset V) (J:Finset U) (n:ℕ) (b:ℝ) (cross:ℕ→ℝ)
    (hhist:ordinaryHostResources (ordinaryHistoryRim Q R S n) (ordinaryHistorySpokes H R S n)=A)
    (hstate:ordinaryHostResources G Hs=A)
    (hinit:∀v∉I,|((Q.neighborFinset v∩I).card:ℝ)-2*(J.filter (H v)).card|≤b)
    (hsub:∀i<n,R i≤ordinaryHistoryRim Q R S i ∧ ∀v u,S i v u→ ordinaryHistorySpokes H R S i v u)
    (hcross:∀i<n,∀v∉I,|(((R i).neighborFinset v∩I).card:ℝ)-2*(J.filter (S i v)).card|≤cross i):
    ∀v∉I,|((G.neighborFinset v∩I).card:ℝ)-2*(J.filter (Hs v)).card|≤b+∑j∈Finset.range n,cross j :=by
  let Qs:=ordinaryHistoryRim Q R S
  let Hseq:=ordinaryHistorySpokes H R S
  have hQ0:Qs 0=Q:=by ext x y;simp [Qs,ordinaryHistoryRim,ordinaryDeletionHistory]
  have hH0:Hseq 0=H:=by funext v u;simp [Hseq,ordinaryHistorySpokes,ordinarySpokesAfterPhysicalDeletion,ordinaryDeletionHistory]
  have hinit':∀v∉I,|(((Qs 0).neighborFinset v∩I).card:ℝ)-2*(J.filter (Hseq 0 v)).card|≤b:=by
    intro v hv
    rw [hQ0,hH0]
    convert hinit v hv using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hstep:∀i<n,Qs (i+1)=Qs i\R i ∧ Hseq (i+1)=fun v u=>Hseq i v u∧¬S i v u:=by
    intro i hi
    exact ⟨ordinary_history_rim_step Q R S i,ordinary_history_spokes_step H R S i⟩
  have hh:=ordinary_cross_balance_deletion_chain Qs R Hseq S I J n b cross hinit' hstep hsub hcross n le_rfl
  obtain ⟨hG,hH⟩:=ordinaryHostResources_injective G (ordinaryHistoryRim Q R S n) Hs
    (ordinaryHistorySpokes H R S n) (hstate.trans hhist.symm)
  intro v hv
  rw [hG,hH]
  convert hh v hv using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
