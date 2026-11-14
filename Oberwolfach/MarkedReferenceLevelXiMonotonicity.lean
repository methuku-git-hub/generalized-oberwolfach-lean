module

public import Oberwolfach.MarkedReferenceLevelData

@[expose] public section
/-! Increasing the permitted size of the inner pair preserves the same
reference-level objects and all other hypotheses. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {Gamma Color:Type} [Fintype Gamma] [Fintype Color]
variable {r d N NI Kgeom:ℕ}
variable {gamma rho omega t p0 betaA aLoA BA kappa ξ ξ' thetaDeep alphaInner omegaInner
  iota β aLo B η x omegaI hIcut deltaI etaBal:ℝ}

def marked_reference_level_increase_xi
    (level:MarkedReferenceLevelData Gamma Color r d N NI Kgeom gamma rho omega t p0 betaA aLoA BA
      kappa ξ thetaDeep alphaInner omegaInner iota β aLo B η x omegaI hIcut deltaI etaBal)
    (hξ:ξ≤ξ') :
    MarkedReferenceLevelData Gamma Color r d N NI Kgeom gamma rho omega t p0 betaA aLoA BA
      kappa ξ' thetaDeep alphaInner omegaInner iota β aLo B η x omegaI hIcut deltaI etaBal := by
  letI:Fintype level.VP:=level.inst7
  letI:Fintype level.V:=level.inst13
  letI:Fintype level.U:=level.inst15
  refine { level with
    hIsize:=level.hIsize.trans (mul_le_mul_of_nonneg_right hξ (Nat.cast_nonneg _))
    hJsize:=level.hJsize.trans (mul_le_mul_of_nonneg_right hξ (Nat.cast_nonneg _))
    hinnerSize:=?_ }
  exact level.hinnerSize.trans (mul_le_mul_of_nonneg_right hξ (Nat.cast_nonneg _))
end Oberwolfach
