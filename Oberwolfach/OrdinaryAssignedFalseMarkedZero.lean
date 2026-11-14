module

public import Oberwolfach.OrdinaryAssignedClassRecipe

@[expose] public section
/-! The ordinary assigned sampling recipe gives zero probability to the
false marked-start colour. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_assigned_false_marked_probability_zero
    {n K:ℕ} {U:Type} [Fintype U]
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (θ c:ℝ) (u:U):ordinaryAssignedMarkedProbability F hF K θ c u false=0:=by
  simp [ordinaryAssignedMarkedProbability]
end Oberwolfach
