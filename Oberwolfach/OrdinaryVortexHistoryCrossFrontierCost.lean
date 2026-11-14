module

public import Oberwolfach.OrdinaryVortexHistoryCrossWindowCost
public import Oberwolfach.OrdinaryDeepBoundaryCrossBound

@[expose] public section
/-! Old protected deletions cost zero in cross balance. The single frontier
level is charged only its deep-boundary cost; newer levels use total cost. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 26000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem ordinary_vortex_history_cross_frontier_cost
    (P Q G:SimpleGraph V) (H Hs:V→U→Prop) (R:ℕ→SimpleGraph V) (S:ℕ→V→U→Prop)
    (D m:ℕ) (β ε:ℝ) (Vort:Vortex U P D β ε m) (buffer i:ℕ) (hbuffer:2≤buffer)
    (A:Finset (Sym2 V⊕(V×U))) (b:ℝ) (cost deepCost:ℕ→ℝ):
    let Iglobal:=Vort.extendedVertices (i+2);let Jglobal:=Vort.extendedIndices (i+2);
    let recent:=Finset.Icc (i+3-buffer) i;
    let cross:=fun t=>if t∈recent then 2*cost t else if t+buffer=i+2 then 2*deepCost t else 0;
    let f:=markedVortexVertexEmbedding Vort (i+1);let g:=markedVortexHubEmbedding Vort (i+1);
    let I:=markedVortexInnerVertices Vort (i+1);let J:=markedVortexInnerHubs Vort (i+1);
    ordinaryHostResources (ordinaryHistoryRim Q R S (i+1)) (ordinaryHistorySpokes H R S (i+1))=A→
    ordinaryHostResources G Hs=A→
    (∀v∈Vort.extendedVertices (i+1),v∉Iglobal→|((Q.neighborFinset v∩Iglobal).card:ℝ)-2*(Jglobal.filter (H v)).card|≤b)→
    (∀j < i+1,R j≤ordinaryHistoryRim Q R S j ∧ ∀v u,S j v u→ ordinaryHistorySpokes H R S j v u)→
    (∀j < i+1,Disjoint (ordinaryPhysicalGraph (R j) (S j))
      (ordinaryDeepBlocker (Vort.extendedVertices (j+buffer)) (Vort.extendedIndices (j+buffer))))→
    (∀j < i+1,∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph (R j) (S j))
      (ordinaryInnerVertices (Vort.extendedVertices (j+1)) (Vort.extendedIndices (j+1)))).degree w:ℝ)≤cost j)→
    (∀j < i+1,∀w:V⊕U,((spanningRestriction (ordinaryBoundaryGraph (R j) (S j)
      (Vort.extendedVertices (j+buffer)) (Vort.extendedIndices (j+buffer)))
      (ordinaryInnerVertices (Vort.extendedVertices (j+1)) (Vort.extendedIndices (j+1)))).degree w:ℝ)≤deepCost j)→
    ∀v,v∉I→|(((G.comap f).neighborFinset v∩I).card:ℝ)-
      2*(J.filter (fun u=>Hs (f v) (g u))).card|≤b+∑j∈Finset.range (i+1),cross j :=by
  intro Iglobal Jglobal recent cross f g I J hhist hstate hinit hsub hprotect hcost hdeep
  have hcross:∀j < i+1,∀v∈Vort.extendedVertices (i+1),v∉Iglobal→
      |(((R j).neighborFinset v∩Iglobal).card:ℝ)-2*(Jglobal.filter (S j v)).card|≤cross j:=by
    intro j hj v hv hvout
    by_cases hw:j∈recent
    · have hIX:Iglobal⊆Vort.extendedVertices (j+1):=Vort.extendedVertices_subset (by omega)
      have hJZ:Jglobal⊆Vort.extendedIndices (j+1):=Vort.extendedIndices_subset (by omega)
      have hvX:v∈Vort.extendedVertices (j+1):=(Vort.extendedVertices_subset (by omega)) hv
      have hh:=ordinary_physical_cost_cross_bound (R j) (S j) (Vort.extendedVertices (j+1)) Iglobal
        (Vort.extendedIndices (j+1)) Jglobal hIX hJZ v hvX (cost j) (hcost j hj)
      simpa [cross,hw] using hh
    · have hjnot:¬(i+3-buffer ≤ j ∧ j ≤ i):=by simpa only [recent,Finset.mem_Icc] using hw
      by_cases hf:j+buffer=i+2
      · have hIT:Iglobal⊆Vort.extendedVertices (j+buffer):=Vort.extendedVertices_subset (by omega)
        have hIX:Iglobal⊆Vort.extendedVertices (j+1):=Vort.extendedVertices_subset (by omega)
        have hJW:Jglobal⊆Vort.extendedIndices (j+buffer):=Vort.extendedIndices_subset (by omega)
        have hJZ:Jglobal⊆Vort.extendedIndices (j+1):=Vort.extendedIndices_subset (by omega)
        have hvX:v∈Vort.extendedVertices (j+1):=(Vort.extendedVertices_subset (by omega)) hv
        have hh:=ordinary_deep_boundary_cross_bound (R j) (S j) (Vort.extendedVertices (j+1))
          (Vort.extendedVertices (j+buffer)) Iglobal (Vort.extendedIndices (j+1))
          (Vort.extendedIndices (j+buffer)) Jglobal hIT hIX hJW hJZ v hvX (deepCost j)
          (hprotect j hj) (by intro w;convert hdeep j hj w using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
        simpa [cross,hw,hf] using hh
      · have hvT:v∈Vort.extendedVertices (j+buffer):=(Vort.extendedVertices_subset (by omega)) hv
        have hIT:Iglobal⊆Vort.extendedVertices (j+buffer):=Vort.extendedVertices_subset (by omega)
        have hJW:Jglobal⊆Vort.extendedIndices (j+buffer):=Vort.extendedIndices_subset (by omega)
        have hh:=ordinary_protected_inner_cross_zero (R j) (S j) (Vort.extendedVertices (j+buffer)) Iglobal
          (Vort.extendedIndices (j+buffer)) Jglobal hIT hJW v hvT (hprotect j hj)
        simpa [cross,hw,hf] using le_of_eq hh
  exact ordinary_vortex_history_local_cross_balance_on_parent P Q G H Hs R S D m β ε Vort i A b cross hhist hstate hinit hsub hcross
end Oberwolfach
