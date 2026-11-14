module

public import Oberwolfach.OrdinaryVortexUniformHistoryCrossFrontier

@[expose] public section
/-! At buffer two, the current outer-to-inner balance pays only the
immediately preceding protected boundary cost. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 22000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem ordinary_vortex_uniform_two_step_cross_balance
    (P Q G:SimpleGraph V) (H Hs:V→U→Prop) (D m:ℕ) (β ε:ℝ)
    (Vort:Vortex U P D β ε m) (r i L:ℕ) (hi:i<L)
    (cost deepCost:ℕ→ℝ) (A:Finset (Sym2 V⊕(V×U))) (inner cross:ℕ→ℕ→ℝ) (b:ℝ)
    (hist:OrdinaryUniformProtectedBalanceHistory Q H
      (fun t=>Vort.extendedVertices (t+1)) (fun t=>Vort.extendedVertices (t+2))
      (fun t=>Vort.extendedIndices (t+1)) (fun t=>Vort.extendedIndices (t+2))
      cost deepCost r (i+1) L A (fun t=>Vort.extendedVertices (t+2))
      (fun t=>Vort.extendedVertices (t+1)) (fun t=>Vort.extendedIndices (t+2))
      (fun t=>Finset.Icc (t+3-2) t) inner cross)
    (hstate:ordinaryHostResources G Hs=A)
    (hinit:∀v∈Vort.extendedVertices (i+1),v∉Vort.extendedVertices (i+2)→
      |((Q.neighborFinset v∩Vort.extendedVertices (i+2)).card:ℝ)-
        2*((Vort.extendedIndices (i+2)).filter (H v)).card|≤b):
    let f:=markedVortexVertexEmbedding Vort (i+1);let g:=markedVortexHubEmbedding Vort (i+1);
    let I:=markedVortexInnerVertices Vort (i+1);let J:=markedVortexInnerHubs Vort (i+1);
    ∀v,v∉I→|(((G.comap f).neighborFinset v∩I).card:ℝ)-
      2*(J.filter (fun u=>Hs (f v) (g u))).card|≤b+2*deepCost i:=by
  intro f g I J
  have h:=ordinary_vortex_uniform_history_cross_frontier P Q G H Hs D m β ε Vort r 2 i L (by omega)
    cost deepCost A inner cross b hist hi hstate hinit
  have hsum:(∑t∈Finset.range (i+1),
      (if t∈Finset.Icc (i+3-2) i then 2*cost t else if t+2=i+2 then 2*deepCost t else 0))=2*deepCost i:=by
    simp
  intro v hv
  have hv' := h v hv
  rw [hsum] at hv'
  exact hv'
end Oberwolfach
