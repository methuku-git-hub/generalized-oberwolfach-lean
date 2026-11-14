module

public import Oberwolfach.OrdinaryHistoryBoundaryBalanceChain
public import Oberwolfach.OrdinaryDecomposedProtectedTrace

@[expose] public section
/-! The boundary-discrepancy estimate applies to the actual host represented
by the same protected wheel-deletion history. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_actual_trace_boundary_balance
    (Q G:SimpleGraph V) (H Hs:V→U→Prop) (R:ℕ→SimpleGraph V) (S:ℕ→V→U→Prop)
    (A:Finset (Sym2 V⊕(V×U))) (I:Finset V) (J:Finset U) (r n:ℕ) (b:ℝ) (boundary:ℕ→ℝ)
    (hhist:ordinaryHostResources (ordinaryHistoryRim Q R S n) (ordinaryHistorySpokes H R S n)=A)
    (hstate:ordinaryHostResources G Hs=A)
    (hinit:∀v∈I,|((spanningRestriction Q I).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>H v u∧v∈I∧u∈J)).card|≤b)
    (hsub:∀i<n,R i≤ordinaryHistoryRim Q R S i ∧ ∀v u,S i v u→ ordinaryHistorySpokes H R S i v u)
    (hdec:∀i<n,HasOrdinaryWheelDecomposition (R i) (S i) r)
    (hboundary:∀i<n,∀v∈I,|(((R i)\spanningRestriction (R i) I).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>S i v u∧¬(v∈I∧u∈J))).card|≤boundary i):
    ∀v∈I,|((spanningRestriction G I).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>Hs v u∧v∈I∧u∈J)).card|≤b+∑j∈Finset.range n,boundary j :=by
  obtain ⟨hG,hH⟩:=ordinaryHostResources_injective G (ordinaryHistoryRim Q R S n) Hs
    (ordinaryHistorySpokes H R S n) (hstate.trans hhist.symm)
  have hh:=ordinary_history_boundary_balance_chain Q H R S I J r n b boundary hinit hsub hdec hboundary
  intro v hv
  rw [hG,hH]
  convert hh v hv using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
