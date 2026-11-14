module

public import Oberwolfach.OrdinaryVortexFutureWheelBoundaryFromCost
public import Oberwolfach.OrdinaryProtectedHostCoverDownWithProperty

@[expose] public section
/-! Preserve the exact selected wheel family while attaching the automatic
coarse future-level discrepancy bounds. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 22000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_vortex_coverdown_future_balance_from_cost
    (P G F:SimpleGraph V) (H:V→U→Prop) (D m:ℕ) (β ε:ℝ) (Q:Vortex U P D β ε m)
    (r i L buffer:ℕ) (cost deepCost:ℝ)
    (hstep:OrdinaryProtectedHostCoverDownResult G F H (Q.extendedVertices (i+1)) (Q.extendedVertices (i+buffer))
      (Q.extendedIndices (i+1)) (Q.extendedIndices (i+buffer)) r cost deepCost):
    OrdinaryProtectedHostCoverDownWithProperty G F H (Q.extendedVertices (i+1)) (Q.extendedVertices (i+buffer))
      (Q.extendedIndices (i+1)) (Q.extendedIndices (i+buffer)) r cost deepCost
      (fun R S=>
        (∀target<L,i∈Finset.Icc (target+3-buffer) target→∀v∈Q.extendedVertices (target+2),
          ordinaryWheelInnerBoundaryError R S (Q.extendedVertices (target+2)) (Q.extendedIndices (target+2)) v≤2*cost) ∧
        (∀target<L,i∈Finset.Icc (target+3-buffer) target→∀v∈Q.extendedVertices (target+1),v∉Q.extendedVertices (target+2)→
          ordinaryWheelCrossError R S (Q.extendedVertices (target+2)) (Q.extendedIndices (target+2)) v≤2*cost)) :=by
  obtain ⟨R,S,hR,hS,hdec,hroot,hbal,hdiv,hdeg,hdeep,havoid⟩:=hstep
  have hUniversal:HasOrdinaryWheelDecomposition R S r:=by
    exact resource_decomposition_map ordinaryWheelResources ordinaryWheelResources
      ordinaryWheelUniversal ordinaryWheelUniversal_resources (ordinaryHostResources R S) hdec
  have hprop:=ordinary_vortex_future_wheel_boundary_from_cost P R S D m β ε Q r i L buffer cost hUniversal hdeg
  exact ⟨R,S,hR,hS,hdec,hroot,hbal,hdiv,hdeg,hdeep,havoid,hprop⟩
end Oberwolfach
