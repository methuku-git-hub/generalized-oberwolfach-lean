module

public import Mathlib.Tactic

@[expose] public section
/-! Arithmetic behind the ordinary caller's prescribed-position capacity.
All variables are the coefficients appearing in the displayed bounds;
`smallTail` accounts for the fixed-order terms and the ceiling. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_position_capacity_from_displayed_bounds
    (n θ C ε lam invd inva A Z v tail:ℝ)
    (hn:0≤n) (hθ:0≤θ) (hC:1≤C)
    (hε:0≤ε) (hlam:0≤lam) (hinvd:0≤ invd) (hinva:0≤ inva)
    (hearly:C*(ε+ε^2*inva)≤1/100000)
    (hlate:C*invd+C*lam+C*lam*inva≤θ/100000)
    (hA:A≤(2*invd+lam)*n)
    (hZ:Z≤(2*θ*ε+2*lam)*n)
    (hv:v≤4*C*(θ*ε^2+lam*ε)*inva*n+tail)
    (smallTail:8*tail+10≤θ*n/16):
    8*A+8*v+4*Z+10≤θ*n/4 := by
  have hC0:0≤C:=by linarith
  have heps2:0≤C*ε^2*inva:=by positivity
  have heps:C*ε≤1/100000:=by nlinarith only [hearly,heps2]
  have hepsle:ε≤1:=by nlinarith only [heps,mul_nonneg (show 0≤C-1 by linarith) hε]
  have hquad:C*ε^2*inva≤1/100000:=by nlinarith only [hearly,heps, hC, hε]
  have hp:invd≤θ/100000:=by nlinarith only [hlate, hlam, hC0, mul_nonneg (show 0≤C-1 by linarith) hinvd, mul_nonneg (mul_nonneg hC0 hlam) hinva]
  have hl:lam≤θ/100000:=by nlinarith only [hlate, hinvd, hC0, mul_nonneg (show 0≤C-1 by linarith) hlam, mul_nonneg (mul_nonneg hC0 hlam) hinva]
  have hlcross:C*lam*inva≤θ/100000:=by nlinarith only [hlate,mul_nonneg hC0 hinvd,mul_nonneg hC0 hlam]
  have ha: C*lam*ε*inva≤θ/100000:=by
    nlinarith only [hlcross, mul_nonneg (mul_nonneg (mul_nonneg hC0 hlam) hinva) (show 0≤1-ε by linarith)]
  have hb:C*θ*ε^2*inva≤θ/100000:=by
    nlinarith only [mul_nonneg hθ (show 0≤1/100000-C*ε^2*inva by linarith)]
  have he:θ*ε≤θ/100000:=by
    have hh:ε≤1/100000:=by nlinarith only [heps,mul_nonneg (show 0≤C-1 by linarith) hε]
    nlinarith only [mul_nonneg hθ (show 0≤1/100000-ε by linarith)]
  have hcoef:16*invd+16*lam+32*C*(θ*ε^2+lam*ε)*inva+8*θ*ε≤θ/8:=by nlinarith only [hp,hl,ha,hb,he,hθ]
  have hcoefn:=mul_le_mul_of_nonneg_right hcoef hn
  nlinarith only [hA,hZ,hv,hcoefn,smallTail,hθ,hn]
end Oberwolfach
