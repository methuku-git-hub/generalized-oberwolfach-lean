module

public import Oberwolfach.Vortex

@[expose] public section
/-! A host's factor count determines the vortex index density. -/
set_option autoImplicit false
namespace Oberwolfach

theorem long_assigned_vortex_density_identity
    (U:Type) [Fintype U] (D:ℕ) (ρ:ℝ) (hD:0<D)
    (hsize:ρ*(D:ℝ)=2*Fintype.card U):
    ρ=initialIndexDensity U D := by
  have hD0:(D:ℝ)≠0:=by exact_mod_cast (Nat.ne_of_gt hD)
  dsimp [initialIndexDensity]
  apply (eq_div_iff hD0).2
  exact hsize
end Oberwolfach
