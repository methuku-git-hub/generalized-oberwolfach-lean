module

public import Oberwolfach.OrdinaryVortexHistoryWindowBoundaryBalance
public import Oberwolfach.OrdinaryVortexInnerBalanceInducedTransport

@[expose] public section
/-! The boundary discrepancies of the actual recent wheel deletions give
the near-balance input on the local inner pair, on the same host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 26000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem ordinary_vortex_history_window_local_balance
    (P Q G:SimpleGraph V) (H Hs:V→U→Prop) (R:ℕ→SimpleGraph V) (S:ℕ→V→U→Prop)
    (D m:ℕ) (β ε:ℝ) (Vort:Vortex U P D β ε m) (buffer i r:ℕ) (hbuffer:2≤buffer)
    (A:Finset (Sym2 V⊕(V×U))) (b η:ℝ) (boundary:ℕ→ℝ):
    let Iglobal:=Vort.extendedVertices (i+2);let Jglobal:=Vort.extendedIndices (i+2);
    let window:=Finset.Icc (i+3-buffer) i;
    let f:=markedVortexVertexEmbedding Vort (i+1);let g:=markedVortexHubEmbedding Vort (i+1);
    let I:=markedVortexInnerVertices Vort (i+1);let J:=markedVortexInnerHubs Vort (i+1);
    ordinaryHostResources (ordinaryHistoryRim Q R S (i+1)) (ordinaryHistorySpokes H R S (i+1))=A→
    ordinaryHostResources G Hs=A→
    (∀v∈Iglobal,|((spanningRestriction Q Iglobal).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>H v u∧v∈Iglobal∧u∈Jglobal)).card|≤b)→
    (∀j < i+1,R j≤ordinaryHistoryRim Q R S j ∧ ∀v u,S j v u→ ordinaryHistorySpokes H R S j v u)→
    (∀j < i+1,HasOrdinaryWheelDecomposition (R j) (S j) r)→
    (∀j < i+1,Disjoint (ordinaryPhysicalGraph (R j) (S j))
      (ordinaryDeepBlocker (Vort.extendedVertices (j+buffer)) (Vort.extendedIndices (j+buffer))))→
    (∀j∈window,∀v∈Iglobal,|(((R j)\spanningRestriction (R j) Iglobal).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>S j v u∧¬(v∈Iglobal∧u∈Jglobal))).card|≤boundary j)→
    b+∑j∈window,boundary j≤η*I.card→
    ∀v:I,|(((G.comap f).induce (I:Set _)).degree v:ℝ)-
      2*(Finset.univ.filter (fun u:J=>Hs (f v.val) (g u.val))).card|≤η*I.card :=by
  intro Iglobal Jglobal window f g I J hhist hstate hinit hsub hdec hprotect hboundary hbudget
  have hamb:=ordinary_vortex_history_window_boundary_balance P Q G H Hs R S D m β ε Vort buffer i r hbuffer A b boundary
    hhist hstate hinit hsub hdec hprotect hboundary
  have hlocal:=ordinary_vortex_inner_balance_induced_transport P G Hs D m β ε Vort i (b+∑j∈window,boundary j) hamb
  intro v
  exact (hlocal v).trans hbudget
end Oberwolfach
