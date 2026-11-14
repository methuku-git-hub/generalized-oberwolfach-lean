module

public import Oberwolfach.OrdinaryInitialPlacementRateObstruction

@[expose] public section

/-! The whole-inner-set target capacity has a second rate incompatibility.
This concerns the displayed sufficient estimates, not the main theorem. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_initial_target_capacity_obstruction
    (ε ρ₀ δinitial η δplacement θ z:ℝ)
    (hε:0<ε) (hδi:δinitial≤1)
    (hsmall:15*η≤min δinitial (δinitial*(ρ₀/8))*ε/2)
    (hδp:0≤δplacement) (hδp1:δplacement≤1)
    (hcap:5*Real.sqrt δplacement≤η)
    (hθ:θ≤δplacement/8) (hz:4*z≤θ/8) (hinner:ε/2≤z):False :=by
  have hrate:δplacement≤η:=ordinary_sqrt_cap_controls_residual_rate δplacement η hδp hδp1 hcap
  have hmin:min δinitial (δinitial*(ρ₀/8))≤1:=(min_le_left _ _).trans hδi
  have hscaled:=mul_le_mul_of_nonneg_right hmin hε.le
  nlinarith only [hsmall,hscaled,hrate,hθ,hz,hinner,hε]

theorem ordinary_first_inner_size_forces_target_rate
    {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
    (P:SimpleGraph V) (D mv:ℕ) (β ε z:ℝ) (Q:Vortex U P D β ε mv)
    (hε:0<ε) (hm:0<mv) (hn:0<Fintype.card V)
    (hinner:((Q.extendedVertices 1).card:ℝ)≤z*Fintype.card V):
    ε/2≤z :=by
  have hh:=ordinary_first_inner_size_forces_placement_rate P D mv β ε (8*z) Q hε hm hn (by
    convert hinner using 1 <;> ring)
  linarith
end Oberwolfach
