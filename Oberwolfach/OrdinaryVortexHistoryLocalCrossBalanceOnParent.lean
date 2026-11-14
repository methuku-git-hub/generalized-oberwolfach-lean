module

public import Oberwolfach.OrdinaryActualTraceCrossBalanceOnParent
public import Oberwolfach.OrdinaryCrossBalanceInducedTransportOnParent
public import Oberwolfach.MarkedFixedVortexGeometry

@[expose] public section
/-! Transfer cross-balance from the actual vortex deletion history to the
local parent used by the root-reference construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem ordinary_vortex_history_local_cross_balance_on_parent
    (P Q G:SimpleGraph V) (H Hs:V→U→Prop) (R:ℕ→SimpleGraph V) (S:ℕ→V→U→Prop)
    (D m:ℕ) (β ε:ℝ) (Vort:Vortex U P D β ε m) (i:ℕ)
    (A:Finset (Sym2 V⊕(V×U))) (b:ℝ) (cross:ℕ→ℝ):
    let Iglobal:=Vort.extendedVertices (i+2);let Jglobal:=Vort.extendedIndices (i+2);
    let f:=markedVortexVertexEmbedding Vort (i+1);let g:=markedVortexHubEmbedding Vort (i+1);
    let I:=markedVortexInnerVertices Vort (i+1);let J:=markedVortexInnerHubs Vort (i+1);
    ordinaryHostResources (ordinaryHistoryRim Q R S (i+1)) (ordinaryHistorySpokes H R S (i+1))=A→
    ordinaryHostResources G Hs=A→
    (∀v∈Vort.extendedVertices (i+1),v∉Iglobal→|((Q.neighborFinset v∩Iglobal).card:ℝ)-2*(Jglobal.filter (H v)).card|≤b)→
    (∀j < i+1,R j≤ordinaryHistoryRim Q R S j ∧ ∀v u,S j v u→ ordinaryHistorySpokes H R S j v u)→
    (∀j < i+1,∀v∈Vort.extendedVertices (i+1),v∉Iglobal→|(((R j).neighborFinset v∩Iglobal).card:ℝ)-2*(Jglobal.filter (S j v)).card|≤cross j)→
    ∀v,v∉I→|(((G.comap f).neighborFinset v∩I).card:ℝ)-
      2*(J.filter (fun u=>Hs (f v) (g u))).card|≤b+∑j∈Finset.range (i+1),cross j :=by
  intro Iglobal Jglobal f g I J hhist hstate hinit hsub hcross
  have hamb:=ordinary_actual_trace_cross_balance_on_parent Q G H Hs R S A Iglobal (Vort.extendedVertices (i+1)) Jglobal (i+1) b cross hhist hstate hinit hsub hcross
  have hI:Iglobal⊆Vort.extendedVertices (i+1):=Vort.extendedVertices_subset (by omega)
  have hJ:Jglobal⊆Vort.extendedIndices (i+1):=Vort.extendedIndices_subset (by omega)
  have hlocal:=ordinary_cross_balance_induced_transport_on_parent G Hs (Vort.extendedVertices (i+1)) Iglobal
    (Vort.extendedIndices (i+1)) Jglobal hI hJ (b+∑j∈Finset.range (i+1),cross j) hamb
  intro v hv
  have hh:=hlocal v hv
  convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
