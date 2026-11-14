module

public import Oberwolfach.OrdinaryGlobalCorrectionSampleInputs
public import Oberwolfach.Vortex

@[expose] public section
/-! The exact sample mean balance is forced by the original index density. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_global_mean_from_density
    (U:Type) [Fintype U] (D:ℕ) (hD:0<D) (pR pH:ℝ)
    (hp:pR=initialIndexDensity U D*pH):
    pR*D=2*pH*Fintype.card U:=by
  have hD0:(D:ℝ)≠0:=by exact_mod_cast (ne_of_gt hD)
  rw [hp]
  dsimp [initialIndexDensity]
  field_simp
  <;> ring
end Oberwolfach
