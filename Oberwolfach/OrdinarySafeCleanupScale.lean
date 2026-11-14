module

public import Oberwolfach.OrdinarySparseCleanupParametersExplicit

@[expose] public section
/-! The explicit capped cleanup tolerance used after fresh sampling. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

def ordinarySafeCleanupScale (r:ℕ) (p βe βh ν cap:ℝ):ℝ :=
  min (ordinarySparseCleanupScale r (p^3*(βe/2)/2) (p^2*βh/2) ν/2) cap
end Oberwolfach
