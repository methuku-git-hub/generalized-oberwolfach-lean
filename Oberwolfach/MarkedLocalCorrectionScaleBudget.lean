module

public import Oberwolfach.MarkedRetypedPhysicalDegreeLocal

@[expose] public section
/-! The local correction error can be allocated at the first inner scale. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_local_correction_scale_budget
    (rho c I eta loc:ℝ) (hrho:0<rho) (hc:0≤c) (hI:0≤I)
    (heta:eta≤rho*c/8) (hloc:loc≤c*I/8) (hlocR:loc≤rho*c*I/8)
    (hone:1≤c*I/8):
    loc+(I*eta+loc)/rho+1≤c*I/2 :=by
  have ha:I*eta≤rho*c*I/8:=by
    have hh:=mul_le_mul_of_nonneg_left heta hI
    nlinarith
  have hb:(I*eta+loc)/rho≤c*I/4:=by
    apply (div_le_iff₀ hrho).2
    nlinarith [ha,hlocR]
  linarith
end Oberwolfach
