module

public import Oberwolfach.OrdinaryPairingNumericHierarchy

@[expose] public section
/-! Translate the fixed pairing hierarchy and actual domain ratios into
    endpoint size and relative error budgets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach

theorem ordinary_pairing_margins_from_scales
    (p₀ κ K η a lam X N Z pR pH density tR tH L:ℝ)
    (hp₀:0<p₀) (hκ:0<κ) (hη:0<η) (ha:0<a) (hlam:0<lam)
    (hRrate:a*K+2*lam≤p₀/2) (hHrate:a*K+2*lam≤p₀*κ) (herr:6*lam≤η*a)
    (hX:0≤X) (hXN:X≤N) (hN:N≤K*X) (hZ:κ*X≤Z)
    (hpR:p₀≤pR) (hpH:p₀≤pH) (hpH1:pH≤1) (hdensity:(1/2:ℝ)≤density)
    (htR:0≤tR) (htRsmall:tR≤lam*X) (htH:0≤tH) (htHsmall:tH≤lam*X)
    (hL:0≤L) (hLsmall:L≤lam*X):
    a*N+tR+L≤pR*density*X ∧ a*N+tH+L≤pH*Z ∧
    ∀SR SH:ℝ,a*N≤SR→a*N≤SH→
      (tH+2*L)+pH*(tH+L)≤η*SH ∧
      (tR+2*L)+pH*(tR+L)≤η*SR ∧
      (tH+3*L)+pH^2*(tH+L)≤η*SH:=by
  have hlamX:0≤lam*X:=mul_nonneg hlam.le hX
  have hN0:0≤N:=hX.trans hXN
  have hZ0:0≤Z:=(mul_nonneg hκ.le hX).trans hZ
  have hpH0:0≤pH:=hp₀.le.trans hpH
  have hAn:=mul_le_mul_of_nonneg_left hN ha.le
  have hRscaled:=mul_le_mul_of_nonneg_right hRrate hX
  have hHscaled:=mul_le_mul_of_nonneg_right hHrate hX
  have hpd:p₀/2≤pR*density:=by
    have hh:=mul_le_mul hpR hdensity (show (0:ℝ)≤1/2 by norm_num) (hp₀.le.trans hpR)
    nlinarith only [hh]
  have hpdX:=mul_le_mul_of_nonneg_right hpd hX
  have hZp:=mul_le_mul_of_nonneg_left hZ hp₀.le
  have hHp:=mul_le_mul_of_nonneg_right hpH hZ0
  have hRbudget:a*N+tR+L≤pR*density*X:=by
    nlinarith only [hAn,hRscaled,hpdX,htRsmall,hLsmall]
  have hHbudget:a*N+tH+L≤pH*Z:=by
    nlinarith only [hAn,hHscaled,hZp,hHp,htHsmall,hLsmall]
  refine ⟨hRbudget,hHbudget,?_⟩
  intro SR SH hSR hSH
  have hηa:0≤η*a:=mul_nonneg hη.le ha.le
  have hscaled:=mul_le_mul_of_nonneg_right herr hX
  have hglobal:=mul_le_mul_of_nonneg_left hXN hηa
  have hSRη:=mul_le_mul_of_nonneg_left hSR hη.le
  have hSHη:=mul_le_mul_of_nonneg_left hSH hη.le
  have heR:pH*(tR+L)≤tR+L:=by nlinarith [mul_le_mul_of_nonneg_right hpH1 (show 0≤tR+L by linarith)]
  have heH:pH*(tH+L)≤tH+L:=by nlinarith [mul_le_mul_of_nonneg_right hpH1 (show 0≤tH+L by linarith)]
  have hpHsq:pH^2≤1:=by nlinarith [sq_nonneg (1-pH)]
  have heH2:pH^2*(tH+L)≤tH+L:=by nlinarith [mul_le_mul_of_nonneg_right hpHsq (show 0≤tH+L by linarith)]
  constructor
  · nlinarith only [heH,htHsmall,hLsmall,hscaled,hglobal,hSHη,hlamX]
  constructor
  · nlinarith only [heR,htRsmall,hLsmall,hscaled,hglobal,hSRη,hlamX]
  · nlinarith only [heH2,htHsmall,hLsmall,hscaled,hglobal,hSHη,hlamX]
end Oberwolfach
