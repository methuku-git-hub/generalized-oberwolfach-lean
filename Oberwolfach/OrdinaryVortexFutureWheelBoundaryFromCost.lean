module

public import Oberwolfach.OrdinaryUniformProtectedBalanceHistory
public import Oberwolfach.OrdinaryWheelPhysicalCostBoundaryBound
public import Oberwolfach.VortexExtended

@[expose] public section
/-! Every wheel deletion automatically supplies coarse future-level
boundary and cross discrepancies from its recorded physical cost. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 22000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_vortex_future_wheel_boundary_from_cost
    (P R:SimpleGraph V) (S:V→U→Prop) (D m:ℕ) (β ε:ℝ) (Q:Vortex U P D β ε m)
    (r i L buffer:ℕ) (cost:ℝ) (hdec:HasOrdinaryWheelDecomposition R S r)
    (hcost:∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph R S)
      (ordinaryInnerVertices (Q.extendedVertices (i+1)) (Q.extendedIndices (i+1)))).degree w:ℝ)≤cost):
    (∀target<L,i∈Finset.Icc (target+3-buffer) target→∀v∈Q.extendedVertices (target+2),
      ordinaryWheelInnerBoundaryError R S (Q.extendedVertices (target+2)) (Q.extendedIndices (target+2)) v≤2*cost) ∧
    (∀target<L,i∈Finset.Icc (target+3-buffer) target→∀v∈Q.extendedVertices (target+1),v∉Q.extendedVertices (target+2)→
      ordinaryWheelCrossError R S (Q.extendedVertices (target+2)) (Q.extendedIndices (target+2)) v≤2*cost) :=by
  constructor
  · intro target ht hw v hv
    have hi:i≤target:=(Finset.mem_Icc.mp hw).2
    have hI:Q.extendedVertices (target+2)⊆Q.extendedVertices (i+1):=Q.extendedVertices_subset (by omega)
    have hJ:Q.extendedIndices (target+2)⊆Q.extendedIndices (i+1):=Q.extendedIndices_subset (by omega)
    have hcost0:0≤cost:=le_trans (by positivity:(0:ℝ)≤((spanningRestriction (ordinaryPhysicalGraph R S)
      (ordinaryInnerVertices (Q.extendedVertices (i+1)) (Q.extendedIndices (i+1)))).degree (Sum.inl v):ℝ)) (hcost (Sum.inl v))
    exact ordinary_wheel_physical_cost_boundary_bound R S (Q.extendedVertices (i+1)) (Q.extendedVertices (target+2))
      (Q.extendedIndices (i+1)) (Q.extendedIndices (target+2)) r hI hJ cost hcost0 hdec hcost v
  · intro target ht hw v hv hvout
    have hi:i≤target:=(Finset.mem_Icc.mp hw).2
    have hI:Q.extendedVertices (target+2)⊆Q.extendedVertices (i+1):=Q.extendedVertices_subset (by omega)
    have hJ:Q.extendedIndices (target+2)⊆Q.extendedIndices (i+1):=Q.extendedIndices_subset (by omega)
    have hvX:v∈Q.extendedVertices (i+1):=(Q.extendedVertices_subset (by omega)) hv
    exact ordinary_physical_cost_cross_bound R S (Q.extendedVertices (i+1)) (Q.extendedVertices (target+2))
      (Q.extendedIndices (i+1)) (Q.extendedIndices (target+2)) hI hJ v hvX cost hcost
end Oberwolfach
