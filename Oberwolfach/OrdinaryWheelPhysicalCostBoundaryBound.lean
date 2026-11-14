module

public import Oberwolfach.OrdinaryPhysicalCostCrossBound
public import Oberwolfach.OrdinaryOuterHostBalanceRefined
public import Oberwolfach.OrdinaryInnerCrossBalance

@[expose] public section
/-! A decomposed wheel deletion has boundary imbalance at most twice its
recorded physical degree on the current parent. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_wheel_physical_cost_boundary_bound
    (R:SimpleGraph V) (S:V→U→Prop) (X I:Finset V) (Z J:Finset U) (r:ℕ)
    (hIX:I⊆X) (hJZ:J⊆Z) (D:ℝ) (hD:0≤D)
    (hdec:HasOrdinaryWheelDecomposition R S r)
    (hdeg:∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph R S)
      (ordinaryInnerVertices X Z)).degree w:ℝ)≤D):
    ∀v,|((R\spanningRestriction R I).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>S v u∧¬(v∈I∧u∈J))).card|≤2*D :=by
  obtain ⟨hbal,_⟩:=ordinary_wheel_decomposition_balance R S r hdec
  have hfull:∀v,|(R.degree v:ℝ)-2*(Finset.univ.filter (S v)).card|≤0:=by
    intro v
    have heq:(R.degree v:ℝ)=2*(Finset.univ.filter (S v)).card:=by exact_mod_cast hbal v
    rw [heq];norm_num
  have hcross:∀v∈I,|((R.neighborFinset v∩I).card:ℝ)-2*(J.filter (S v)).card|≤2*D:=by
    intro v hv
    exact ordinary_physical_cost_cross_bound R S X I Z J hIX hJZ v (hIX hv) D hdeg
  have hinner:=ordinary_inner_balance_from_cross_profile R S I J (2*D) (by positivity) hcross
  have hh:=ordinary_outer_host_balance_refined R S I J 0 (2*D) hfull hinner
  intro v
  simpa using hh v
end Oberwolfach
