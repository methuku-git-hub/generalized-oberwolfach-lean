module

public import Oberwolfach.OrdinaryInducedParentThreshold

@[expose] public section
/-! The inner parent-density bound supplies the endpoint neighborhood
    condition without an additional root-by-root assumption. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_endpoint_degree_from_inner_density
    {V : Type} [Fintype V] [DecidableEq V] (P : SimpleGraph V) (A : Finset V) (density : ℝ)
    (hthreshold : cycleThreshold 3 ≤ density)
    (hmin : ∀v,density*A.card≤((A∩P.neighborFinset v).card:ℝ)) :
    ∀x∉A,∀v∈insert x A,(3/4:ℝ)*A.card≤((A∩P.neighborFinset v).card:ℝ) := by
  have hlow : (3/4:ℝ) ≤ density := cycleThreshold_triangle_lower.trans hthreshold
  intro x hx v hv
  exact (mul_le_mul_of_nonneg_right hlow (by positivity : (0:ℝ) ≤ A.card)).trans (hmin v)
end Oberwolfach
