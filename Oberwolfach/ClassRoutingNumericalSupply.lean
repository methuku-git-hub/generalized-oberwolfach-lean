module

public import Oberwolfach.BalancedOrientation

@[expose] public section
/-! The dense-host common-neighbour bound pays for the two-path sampling
error and the two incident class-edit losses. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem class_routing_numerical_supply
    {V:Type} [Fintype V] (P:SimpleGraph V) (α p err b:ℝ)
    (hmin:∀v,(1/2+α)*(Fintype.card V:ℝ)≤P.degree v)
    (hsmall:err+2*b≤α*p^2*Fintype.card V):
    ∀x y,x≠y→(α*p^2)*(Fintype.card V)+2*b≤
      ((P.neighborFinset x∩P.neighborFinset y).card:ℝ)*p^2-err:=by
  intro x y _
  have hc:=commonNeighbours_of_minDegree P hmin x y
  have hh:=mul_le_mul_of_nonneg_right hc (sq_nonneg p)
  nlinarith
end Oberwolfach
