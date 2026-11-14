module

public import Oberwolfach.LongEarlyDeletionResidualScale

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_aligned_residual_error
    (epsOrd epsParent ζEarly ξParent:ℝ)
    (hOrd:0<epsOrd) (hParent:epsParent≤epsOrd)
    (hζ:0≤ζEarly) (hζcap:ζEarly≤epsOrd/8)
    (hξ:0≤ξParent) (hξcap:4*ξParent≤epsParent/2):
    ∃ξResidual:ℝ,0≤ξResidual ∧ 4*ξResidual≤epsOrd/2 ∧
      ζEarly≤ξResidual ∧ ξParent≤ξResidual ∧
      ∀n:ℕ,ζEarly*n≤ξResidual*n ∧ ξParent*n≤ξResidual*n := by
  apply long_early_deletion_residual_scale epsOrd ζEarly ξParent hOrd hζ hζcap hξ
  linarith
end Oberwolfach
