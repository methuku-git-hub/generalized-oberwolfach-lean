module

public import Oberwolfach.FirstVortexExplicitBalanceWindowRequiresVortexRatio

@[expose] public section
/-! If the balance tolerance is at most the vortex ratio, the present
coarse global-load interface cannot satisfy its explicit cap. This is an
interface obstruction and says nothing against the original theorem. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_explicit_balance_small_window_obstruction
    {n D m:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (β ε:ℝ) (Q:Vortex U P D β ε m)
    (r:ℕ) (etaBal x εInner δsmall etaGlobal rho:ℝ)
    (hn:0<n) (hε:0<ε) (hm:0<m) (hrho:0<rho) (hrho1:rho≤1)
    (hη:etaBal≤ε)
    (hinner:((Q.extendedVertices 1).card:ℝ)≤εInner*n)
    (hgap:εInner*n≤δsmall*n/4) (hLoss:2*δsmall<etaGlobal)
    (hEta:etaGlobal≤markedExplicitJointLocalCap (r+4) (r+12) etaBal x*rho/4):False :=by
  have hneed:256*((r+4+4:ℕ):ℝ)*ε<rho*etaBal:=
    (first_vortex_explicit_balance_window_requires_vortex_ratio P β ε Q r etaBal x εInner δsmall etaGlobal rho
      hn hε hm hrho hinner hgap hLoss hEta).2
  have hprod:rho*etaBal≤ε:=by
    have hh:=mul_le_mul_of_nonneg_left hη hrho.le
    nlinarith
  have hr:(0:ℝ)≤r:=Nat.cast_nonneg _
  push_cast at hneed
  nlinarith [mul_nonneg hr hε.le]
end Oberwolfach
