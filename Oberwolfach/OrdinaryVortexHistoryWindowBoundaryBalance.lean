module

public import Oberwolfach.OrdinaryActualTraceWindowBoundaryBalance
public import Oberwolfach.OrdinaryVortexBufferedNesting
public import Oberwolfach.OrdinaryProtectedDeepMonotonicity

@[expose] public section
/-! On the same vortex and deletion history, the current inner balance is
charged only to boundary discrepancies from the finite recent window. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_vortex_history_window_boundary_balance
    (P Q G:SimpleGraph V) (H Hs:V→U→Prop) (R:ℕ→SimpleGraph V) (S:ℕ→V→U→Prop)
    (D m:ℕ) (β ε:ℝ) (Vort:Vortex U P D β ε m) (buffer i r:ℕ) (hbuffer:2≤buffer)
    (A:Finset (Sym2 V⊕(V×U))) (b:ℝ) (boundary:ℕ→ℝ):
    let I:=Vort.extendedVertices (i+2);let J:=Vort.extendedIndices (i+2);
    let window:=Finset.Icc (i+3-buffer) i;
    ordinaryHostResources (ordinaryHistoryRim Q R S (i+1)) (ordinaryHistorySpokes H R S (i+1))=A→
    ordinaryHostResources G Hs=A→
    (∀v∈I,|((spanningRestriction Q I).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>H v u∧v∈I∧u∈J)).card|≤b)→
    (∀j < i+1,R j≤ordinaryHistoryRim Q R S j ∧ ∀v u,S j v u→ ordinaryHistorySpokes H R S j v u)→
    (∀j < i+1,HasOrdinaryWheelDecomposition (R j) (S j) r)→
    (∀j < i+1,Disjoint (ordinaryPhysicalGraph (R j) (S j))
      (ordinaryDeepBlocker (Vort.extendedVertices (j+buffer)) (Vort.extendedIndices (j+buffer))))→
    (∀j∈window,∀v∈I,|(((R j)\spanningRestriction (R j) I).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>S j v u∧¬(v∈I∧u∈J))).card|≤boundary j)→
    ∀v∈I,|((spanningRestriction G I).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>Hs v u∧v∈I∧u∈J)).card|≤b+∑j∈window,boundary j :=by
  intro I J window hhist hstate hinit hsub hdec hprotect hboundary
  have hJ:∀j∈window,j < i+1:=by
    intro j hj
    have hh: j ≤ i:=(Finset.mem_Icc.mp hj).2
    omega
  have havoid:∀j < i+1,j∉window→Disjoint (ordinaryPhysicalGraph (R j) (S j)) (ordinaryDeepBlocker I J):=by
    intro j hj hjnot
    have hjnot':¬(i+3-buffer≤j ∧ j ≤ i):=by simpa only [window,Finset.mem_Icc] using hjnot
    have hV:I⊆Vort.extendedVertices (j+buffer):=Vort.extendedVertices_subset (by omega)
    have hU:J⊆Vort.extendedIndices (j+buffer):=Vort.extendedIndices_subset (by omega)
    have hmono:ordinaryDeepBlocker I J≤ordinaryDeepBlocker (Vort.extendedVertices (j+buffer)) (Vort.extendedIndices (j+buffer)):=
      ordinary_deep_blocker_mono I _ J _ hV hU
    exact (hprotect j hj).mono_right hmono
  exact ordinary_actual_trace_window_boundary_balance Q G H Hs R S A I J window r (i+1) b boundary
    hJ hhist hstate hinit hsub hdec havoid hboundary
end Oberwolfach
