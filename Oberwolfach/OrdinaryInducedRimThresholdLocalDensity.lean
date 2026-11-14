module

public import Oberwolfach.OrdinaryInducedParentThreshold

@[expose] public section
/-! Only vertices in the inner set are needed for the induced minimum degree. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_induced_rim_threshold_from_local_density
    {V : Type} [Fintype V] [DecidableEq V] (P : SimpleGraph V) (I : Finset V)
    (density α : ℝ) (hthreshold : cycleThreshold 3 + α ≤ density)
    (hmin : ∀ v ∈ I, density * I.card ≤ ((I ∩ P.neighborFinset v).card : ℝ)) :
    ∀ v : I, (1/2 + α) * I.card ≤ ((P.induce (I : Set V)).degree v : ℝ) := by
  have hhalf : (1/2 : ℝ) ≤ cycleThreshold 3 := cycleThreshold_half_le (by omega)
  have hcoef : (1/2 : ℝ) + α ≤ density := by linarith
  intro v
  have h := (mul_le_mul_of_nonneg_right hcoef (by positivity : (0:ℝ)≤I.card)).trans (hmin v.val v.property)
  rw [induced_degree_intersection P I v]
  simpa only [Finset.inter_comm] using h
end Oberwolfach
