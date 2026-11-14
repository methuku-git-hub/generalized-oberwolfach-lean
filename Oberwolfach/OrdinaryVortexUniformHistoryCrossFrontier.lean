module

public import Oberwolfach.OrdinaryVortexHistoryCrossFrontierCost
public import Oberwolfach.OrdinaryVortexUniformBalanceHistoryAt

@[expose] public section
/-! Apply the frontier estimate to the one recorded wheel-deletion history,
without choosing a different history or a different sampled host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 26000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem ordinary_vortex_uniform_history_cross_frontier
    (P Q G:SimpleGraph V) (H Hs:V→U→Prop) (D m:ℕ) (β ε:ℝ)
    (Vort:Vortex U P D β ε m) (r buffer i L:ℕ) (hbuffer:2≤buffer)
    (cost deepCost:ℕ→ℝ) (A:Finset (Sym2 V⊕(V×U))) (inner cross:ℕ→ℕ→ℝ) (b:ℝ)
    (hist:OrdinaryUniformProtectedBalanceHistory Q H
      (fun t=>Vort.extendedVertices (t+1)) (fun t=>Vort.extendedVertices (t+buffer))
      (fun t=>Vort.extendedIndices (t+1)) (fun t=>Vort.extendedIndices (t+buffer))
      cost deepCost r (i+1) L A
      (fun t=>Vort.extendedVertices (t+2)) (fun t=>Vort.extendedVertices (t+1))
      (fun t=>Vort.extendedIndices (t+2)) (fun t=>Finset.Icc (t+3-buffer) t) inner cross)
    (hi:i<L) (hstate:ordinaryHostResources G Hs=A)
    (hinit:∀v∈Vort.extendedVertices (i+1),v∉Vort.extendedVertices (i+2)→
      |((Q.neighborFinset v∩Vort.extendedVertices (i+2)).card:ℝ)-
        2*((Vort.extendedIndices (i+2)).filter (H v)).card|≤b):
    let recent:=Finset.Icc (i+3-buffer) i;
    let f:=markedVortexVertexEmbedding Vort (i+1);let g:=markedVortexHubEmbedding Vort (i+1);
    let I:=markedVortexInnerVertices Vort (i+1);let J:=markedVortexInnerHubs Vort (i+1);
    ∀v,v∉I→|(((G.comap f).neighborFinset v∩I).card:ℝ)-
      2*(J.filter (fun u=>Hs (f v) (g u))).card|≤b+∑t∈Finset.range (i+1),
      (if t∈recent then 2*cost t else if t+buffer=i+2 then 2*deepCost t else 0):=by
  intro recent f g I J
  have h:=ordinary_vortex_uniform_balance_history_at P Q H D m β ε Vort r i L buffer cost deepCost A inner cross hist hi
  have hsub:∀t < i+1,h.rim t≤ordinaryHistoryRim Q h.rim h.spokes t ∧
      ∀v u,h.spokes t v u→ ordinaryHistorySpokes H h.rim h.spokes t v u:=by
    intro t ht;exact ⟨(h.decomposition t ht).1,(h.decomposition t ht).2.1⟩
  have hprotect:∀t < i+1,Disjoint (ordinaryPhysicalGraph (h.rim t) (h.spokes t))
      (ordinaryDeepBlocker (Vort.extendedVertices (t+buffer)) (Vort.extendedIndices (t+buffer))):=by
    intro t ht;exact (h.levels t ht).2.2
  have hcost:∀t < i+1,∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph (h.rim t) (h.spokes t))
      (ordinaryInnerVertices (Vort.extendedVertices (t+1)) (Vort.extendedIndices (t+1)))).degree w:ℝ)≤cost t:=by
    intro t ht w
    convert (h.levels t ht).1 w using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hdeep:∀t < i+1,∀w:V⊕U,((spanningRestriction (ordinaryBoundaryGraph (h.rim t) (h.spokes t)
      (Vort.extendedVertices (t+buffer)) (Vort.extendedIndices (t+buffer)))
      (ordinaryInnerVertices (Vort.extendedVertices (t+1)) (Vort.extendedIndices (t+1)))).degree w:ℝ)≤deepCost t:=by
    intro t ht w
    convert (h.levels t ht).2.1 w using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  exact ordinary_vortex_history_cross_frontier_cost P Q G H Hs h.rim h.spokes D m β ε Vort buffer i hbuffer A b cost deepCost
    h.state hstate hinit hsub hprotect hcost hdeep
end Oberwolfach
