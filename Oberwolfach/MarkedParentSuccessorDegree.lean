module

public import Oberwolfach.SuccessorWeightsTheorem

@[expose] public section
/-! The marked preparation's displayed ratio margin supplies the minimum
degree condition of the constructed successor weights. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]
theorem marked_parent_successor_degree (r k₀:ℕ) (hlen:r+5=(k₀+2)*2) (α:ℝ)
    (hmargin:successorCycleRatio k₀+α/2≤1/2+α)
    (P:SimpleGraph V) (hP:∀ v,(1/2+α)*Fintype.card V≤(P.degree v:ℝ)):
    ∀ v,(((r+5:ℕ):ℝ)/(2*((r+5:ℕ):ℝ)-2)+α/2)*Fintype.card V≤(P.degree v:ℝ) := by
  intro v
  have heq:((r+5:ℕ):ℝ)/(2*((r+5:ℕ):ℝ)-2)=successorCycleRatio k₀:=by
    rw [hlen]
    exact (successorCycleRatio_standard k₀).symm
  rw [heq]
  exact (mul_le_mul_of_nonneg_right hmargin (by positivity)).trans (hP v)
end Oberwolfach
