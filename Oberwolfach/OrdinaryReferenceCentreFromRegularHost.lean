module

public import Oberwolfach.OrdinaryBalancedMatchingReservoirEvent

@[expose] public section
/-! The reference balance centres agree by the original host degree and the
    reserved-class sampling marginal. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V]

theorem ordinary_reference_centre_from_regular_host
    (P:SimpleGraph V) (D:ℕ) (hP:P.IsRegularOfDegree D)
    (ρ rsv p:ℝ) (hsize:ρ*D=2*(Fintype.card U:ℝ)) (hp:2*p=ρ*rsv):
    ∀v,(2*p)*(P.degree v:ℝ)=2*(rsv*Fintype.card U):=by
  intro v
  rw [hP v]
  rw [hp]
  calc
    (ρ*rsv)*(D:ℝ)=rsv*(ρ*D):=by ring
    _=2*(rsv*Fintype.card U):=by rw [hsize]; ring
end Oberwolfach
