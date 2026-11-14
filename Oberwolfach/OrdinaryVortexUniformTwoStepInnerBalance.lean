module

public import Oberwolfach.OrdinaryVortexUniformBalanceHistoryAt
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

theorem ordinary_vortex_uniform_two_step_inner_balance
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
        u∈Vort.extendedIndices (i+2))).card|≤b):
    let f:=markedVortexVertexEmbedding Vort (i+1);let g:=markedVortexHubEmbedding Vort (i+1);
    let I:=markedVortexInnerVertices Vort (i+1);let J:=markedVortexInnerHubs Vort (i+1);
    ∀v:I,|(((G.comap f).induce (I:Set _)).degree v:ℝ)-
      2*(Finset.univ.filter (fun u:J=>Hs (f v.val) (g u.val))).card|≤b:=by
  intro f g I J
  have hcert:=ordinary_vortex_uniform_balance_history_at P Q H D m β ε Vort r i L 2 cost deepCost A inner cross hist hi
  have hsub:∀t < i+1,hcert.rim t≤ordinaryHistoryRim Q hcert.rim hcert.spokes t ∧
      ∀v u,hcert.spokes t v u→ ordinaryHistorySpokes H hcert.rim hcert.spokes t v u:=by
    intro t ht
    exact ⟨(hcert.decomposition t ht).1,(hcert.decomposition t ht).2.1⟩
  have hdec:∀t < i+1,HasOrdinaryWheelDecomposition (hcert.rim t) (hcert.spokes t) r:=by
    intro t ht;exact (hcert.decomposition t ht).2.2
  have hprotect:∀t < i+1,Disjoint (ordinaryPhysicalGraph (hcert.rim t) (hcert.spokes t))
      (ordinaryDeepBlocker (Vort.extendedVertices (t+2)) (Vort.extendedIndices (t+2))):=by
    intro t ht;exact (hcert.levels t ht).2.2
  have hamb:=ordinary_vortex_history_window_boundary_balance P Q G H Hs hcert.rim hcert.spokes
    D m β ε Vort 2 i r (by omega) A b (fun _=>0) hcert.state hstate hinit hsub hdec hprotect (by
      intro t ht
      have h:=Finset.mem_Icc.mp ht
      omega)
  have hamb':∀v∈Vort.extendedVertices (i+2),
      |((spanningRestriction G (Vort.extendedVertices (i+2))).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>Hs v u∧v∈Vort.extendedVertices (i+2)∧
        u∈Vort.extendedIndices (i+2))).card|≤b:=by
    intro v hv
    simpa using hamb v hv
  exact ordinary_vortex_inner_balance_induced_transport P G Hs D m β ε Vort i b hamb'
end Oberwolfach
