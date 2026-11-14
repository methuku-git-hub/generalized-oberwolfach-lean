module

public import Oberwolfach.OrdinaryVortexUniformTwoStepCrossBalance
public import Oberwolfach.OrdinaryVortexUniformTwoStepInnerBalance
public import Oberwolfach.OrdinaryVortexHistoryWindowBoundaryBalance
public import Oberwolfach.OrdinaryVortexInnerBalanceInducedTransport

@[expose] public section
/-! With a two-step protected pair, every earlier deletion avoids the
current inner pair. Its inner balance is unchanged, with no cost-window loss. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 25000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem ordinary_vortex_uniform_two_step_both_balance
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
    (hinit:∀v∈Vort.extendedVertices (i+2),
      |((spanningRestriction Q (Vort.extendedVertices (i+2))).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>H v u∧v∈Vort.extendedVertices (i+2)∧
        u∈Vort.extendedIndices (i+2))).card|≤b)
    (hcross:∀v∈Vort.extendedVertices (i+1),v∉Vort.extendedVertices (i+2)→
      |((Q.neighborFinset v∩Vort.extendedVertices (i+2)).card:ℝ)-
        2*((Vort.extendedIndices (i+2)).filter (H v)).card|≤b):
    let f:=markedVortexVertexEmbedding Vort (i+1);let g:=markedVortexHubEmbedding Vort (i+1);
    let I:=markedVortexInnerVertices Vort (i+1);let J:=markedVortexInnerHubs Vort (i+1);
    (∀v:I,|(((G.comap f).induce (I:Set _)).degree v:ℝ)-
      2*(Finset.univ.filter (fun u:J=>Hs (f v.val) (g u.val))).card|≤b) ∧
    (∀v,v∉I→|(((G.comap f).neighborFinset v∩I).card:ℝ)-
      2*(J.filter (fun u=>Hs (f v) (g u))).card|≤b+2*deepCost i):=by
  intro f g I J
  exact ⟨ordinary_vortex_uniform_two_step_inner_balance P Q G H Hs D m β ε Vort r i L hi cost deepCost A inner cross b hist hstate hinit,
    ordinary_vortex_uniform_two_step_cross_balance P Q G H Hs D m β ε Vort r i L hi cost deepCost A inner cross b hist hstate hcross⟩
end Oberwolfach
