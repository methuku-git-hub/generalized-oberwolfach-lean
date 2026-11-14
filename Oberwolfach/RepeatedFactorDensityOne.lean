module

public import Oberwolfach.Vortex

@[expose] public section
/-! Repeating one factor exactly D/2 times gives index density one for a
positive even host degree D. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem repeated_factor_density_one (D:ℕ) (hD:0<D) (hEven:Even D):
    initialIndexDensity (Fin (D/2)) D=1:=by
  have hnum:2*(D/2)=D:=by have hh:=hEven.two_dvd; omega
  have hreal:(2:ℝ)*(D/2:ℕ)=(D:ℝ):=by exact_mod_cast hnum
  have hD0:(D:ℝ)≠0:=by exact_mod_cast (Nat.ne_of_gt hD)
  simp only [initialIndexDensity,Fintype.card_fin,hreal,div_self hD0]
end Oberwolfach
