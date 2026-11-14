module

public import Oberwolfach.OrdinaryCleanupParentProfiles

@[expose] public section
/-! Positive sampling and density gaps permit the two cleanup extension
    margins to be fixed before the order and before sampling. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach

theorem ordinary_cleanup_margin_explicit
    (p₀ δ a K:ℝ) (hp₀:0<p₀) (hδ:0<δ) (ha:0<a) (hK:0<K):
    let cE:=p₀^3*δ; let cH:=p₀^2*a;
    let βe:=cE/(4*K); let βh:=cH/(4*K);
    ∀(n X Z pR pH density tR tH L:ℝ),
      0≤X → n≤K*X → a*X≤Z → p₀≤pR → p₀≤pH → (1/2:ℝ)+δ≤density →
      tR≤(p₀^3*δ)*X/4 → 3*L≤(p₀^3*δ)*X/4 →
      tH≤(p₀^2*a)*X/4 → 2*L≤(p₀^2*a)*X/4 →
      βe*n+tR+3*L≤pR^2*pH*(2*density-1)*X ∧
      βh*n+tH+2*L≤pH^2*Z := by
  intro cE cH βe βh
  have hcE:0<cE:=by dsimp [cE];positivity
  have hcH:0<cH:=by dsimp [cH];positivity
  have hβe:0<βe:=by dsimp [βe];positivity
  have hβh:0<βh:=by dsimp [βh];positivity
  intro n X Z pR pH density tR tH L hX hn hZ hpR hpH hdensity htR hLe htH hLh
  have hβen:βe*n≤cE*X/4:=by
    calc
      βe*n≤βe*(K*X):=mul_le_mul_of_nonneg_left hn hβe.le
      _=cE*X/4:=by dsimp [βe];field_simp [hK.ne'] <;> ring
  have hβhn:βh*n≤cH*X/4:=by
    calc
      βh*n≤βh*(K*X):=mul_le_mul_of_nonneg_left hn hβh.le
      _=cH*X/4:=by dsimp [βh];field_simp [hK.ne'] <;> ring
  have hpR0:0≤pR:=hp₀.le.trans hpR
  have hpH0:0≤pH:=hp₀.le.trans hpH
  have hR2:p₀^2≤pR^2:=by nlinarith [sq_nonneg (pR-p₀)]
  have hH2:p₀^2≤pH^2:=by nlinarith [sq_nonneg (pH-p₀)]
  have hpow:p₀^3≤pR^2*pH:=by
    have hh:=mul_le_mul hR2 hpH hp₀.le (sq_nonneg pR)
    nlinarith only [hh]
  have hgap:2*δ≤2*density-1:=by linarith
  have hcoeff:2*cE≤pR^2*pH*(2*density-1):=by
    have hh:=mul_le_mul hpow hgap (show 0≤2*δ by positivity) (show 0≤pR^2*pH by positivity)
    dsimp [cE]
    nlinarith only [hh]
  have hscaled:=mul_le_mul_of_nonneg_right hcoeff hX
  have hZ0:0≤Z:=le_trans (mul_nonneg ha.le hX) hZ
  have hhub1:=mul_le_mul_of_nonneg_left hZ (sq_nonneg p₀)
  have hhub2:=mul_le_mul_of_nonneg_right hH2 hZ0
  have hhub:cH*X≤pH^2*Z:=by dsimp [cH];nlinarith only [hhub1,hhub2]
  constructor
  · dsimp [cE] at hβen hcE hscaled
    nlinarith only [hβen,htR,hLe,hscaled,hX,hcE.le]
  · dsimp [cH] at hβhn hcH hhub
    nlinarith only [hβhn,htH,hLh,hhub,hX,hcH.le]
end Oberwolfach
