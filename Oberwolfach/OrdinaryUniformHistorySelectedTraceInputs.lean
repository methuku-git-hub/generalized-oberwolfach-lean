module

public import Oberwolfach.OrdinaryUniformProtectedBalanceHistory
public import Oberwolfach.OrdinaryVortexSelectedCostSchedule

@[expose] public section
/-! A uniform protected balance history supplies the actual protected trace
and the selected cost bounds required by a later wheel certificate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_uniform_history_selected_trace_inputs
    {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [LinearOrder U]
    {P:SimpleGraph V} {D mv:ℕ} {β ε:ℝ} (Q:Vortex U P D β ε mv)
    (G:SimpleGraph V) (H:V→U→Prop) (r i L:ℕ) (A:Finset (Sym2 V⊕(V×U)))
    (rate ξ C:ℝ) (hrate:0≤rate) (hξ:0≤ξ) (hC:0≤C)
    (h:OrdinaryUniformProtectedBalanceHistory G H
      (fun k=>Q.extendedVertices (k+1)) (fun k=>Q.extendedVertices (k+2))
      (fun k=>Q.extendedIndices (k+1)) (fun k=>Q.extendedIndices (k+2))
      (ordinaryVortexSelectedCost Q rate) (ordinaryFineDeepCost Q ξ) r (i+1) L A
      (fun t=>Q.extendedVertices (t+2)) (fun t=>Q.extendedVertices (t+1))
      (fun t=>Q.extendedIndices (t+2)) (fun t=>Finset.Icc (t+3-2) t)
      (fun _ _=>0) (fun _ _=>0)):
    OrdinaryProtectedTrace G H
      (fun k=>Q.extendedVertices (k+1)) (fun k=>Q.extendedVertices (k+2))
      (fun k=>Q.extendedIndices (k+1)) (fun k=>Q.extendedIndices (k+2))
      (ordinaryVortexSelectedCost Q rate) (ordinaryFineDeepCost Q ξ) (i+1) A ∧
    (∀t∈Finset.Icc (i+2-2) i,
      0≤ordinaryVortexSelectedCost Q rate t ∧
      ordinaryVortexSelectedCost Q rate t≤
        4*rate*Fintype.card (markedVortexVertexType Q t⊕markedVortexHubType Q t)+C) :=by
  have hdec:OrdinaryDecomposedProtectedTrace G H
      (fun k=>Q.extendedVertices (k+1)) (fun k=>Q.extendedVertices (k+2))
      (fun k=>Q.extendedIndices (k+1)) (fun k=>Q.extendedIndices (k+2))
      (ordinaryVortexSelectedCost Q rate) (ordinaryFineDeepCost Q ξ) r (i+1) A:=
    ⟨h.rim,h.spokes,h.trace⟩
  have hcost:=ordinary_vortex_selected_cost_schedule Q rate ξ C hrate hξ hC
  refine ⟨ordinary_decomposed_protected_trace_forget G H _ _ _ _ _ _ r (i+1) A hdec,?_⟩
  intro t ht
  exact ⟨hcost.1 t,hcost.2.2.1 t⟩
end Oberwolfach
