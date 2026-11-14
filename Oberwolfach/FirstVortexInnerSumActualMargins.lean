module

public import Oberwolfach.FirstVortexInnerSumMargins

@[expose] public section
/-! The actual fixed-spacing and boundary errors fit the summed-loss
budgets once the later component rates are sufficiently small. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_inner_sum_actual_margins
    (n d:ℕ) (I ε c rho eta t s ζ boundary a γ κ:ℝ)
    (hn:0<n) (hI:0≤I) (hIN:I≤n) (hε:0≤ε) (hc:0≤c) (hrho:0≤rho) (heta:0≤eta)
    (ht:0≤t) (hs:0≤s) (hsize:ε*n/2≤I)
    (hζ0:0≤ζ) (hboundary0:0≤boundary) (ha:0≤a) (hγ:0≤γ) (hκ:0≤κ)
    (hζ:ζ≤s) (hboundary:boundary≤s*n) (hmax:max a γ≤s) (hκs:κ≤s)
    (hfixed:((6*d+2:ℕ):ℝ)≤s*n) (hunit:1≤s*n) (hrate:12*s≤t)
    (hpow:(n:ℝ)^(3/5:ℝ)+(d:ℝ)*(n:ℝ)^(3/5:ℝ)≤t*n)
    (hglobal:5*t≤ε*eta/2) (hlocal:5*t≤c*rho*ε/8):
    ∃lossInside inside:ℝ,0≤lossInside ∧ 0≤ inside ∧
      0≤2*(boundary+2*(max a γ*n)+((6*d+2:ℕ):ℝ)+(κ*n+1)) ∧
      I*(ζ*n+2*((6*d+2:ℕ):ℝ))+
        (n:ℝ)*(2*(boundary+2*(max a γ*n)+((6*d+2:ℕ):ℝ)+(κ*n+1)))≤lossInside ∧
      I*((n:ℝ)^(3/5:ℝ)+(d:ℝ)*(n:ℝ)^(3/5:ℝ))+lossInside≤ inside ∧
      inside≤I*eta*n ∧ inside≤c*rho*n*I/4 :=by
  have hnR:0<(n:ℝ):=by exact_mod_cast hn
  have hmax0:0≤max a γ:=le_trans ha (le_max_left _ _)
  have hmaxn:=mul_le_mul_of_nonneg_right hmax hnR.le
  have hκn:=mul_le_mul_of_nonneg_right hκs hnR.le
  have hraten:=mul_le_mul_of_nonneg_right hrate hnR.le
  have houter0:0≤2*(boundary+2*(max a γ*n)+((6*d+2:ℕ):ℝ)+(κ*n+1)):=by positivity
  have houter:2*(boundary+2*(max a γ*n)+((6*d+2:ℕ):ℝ)+(κ*n+1))≤t*n:=by nlinarith
  have hζt:ζ≤t:=by linarith
  have hfixedt:((6*d+2:ℕ):ℝ)≤t*n:=by nlinarith
  have hq0:0≤(n:ℝ)^(3/5:ℝ)+(d:ℝ)*(n:ℝ)^(3/5:ℝ):=by positivity
  obtain ⟨lossInside,inside,hL,hInside,hBound,hBudget,hGlobal,hLocal⟩:=
    first_vortex_inner_sum_margins (n:ℝ) I ε c rho eta t ζ ((6*d+2:ℕ):ℝ)
      (2*(boundary+2*(max a γ*n)+((6*d+2:ℕ):ℝ)+(κ*n+1)))
      ((n:ℝ)^(3/5:ℝ)+(d:ℝ)*(n:ℝ)^(3/5:ℝ))
      hnR hI hIN hε hc hrho heta ht hsize hζ0 (by positivity) houter0 hq0 hζt hfixedt houter hpow hglobal hlocal
  exact ⟨lossInside,inside,hL,hInside,houter0,hBound,hBudget,hGlobal,hLocal⟩
end Oberwolfach
