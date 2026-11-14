module

public import Oberwolfach.OrdinarySmallRootDensity

@[expose] public section
/-! Numerical margin for all common-hub tests of bounded order. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
theorem ordinary_hub_margin_from_density (h:ℕ) (ω smin pH β ε n m:ℝ)
    (hω:0<ω) (hs:0<smin) (hs1:smin≤1) (hp:smin≤pH)
    (hβ:0≤β) (hβmax:β≤ω*smin^h/4)
    (hε:0≤ε) (hεmax:ε≤smin^h/2) (hn:0≤n) (hm:ω*n≤m):
    ∀ k:ℕ,k≤h → β*n+ε*m≤pH^k*m := by
  intro k hk
  have hm0:0≤m:=le_trans (mul_nonneg hω.le hn) hm
  have hpow:smin^h≤pH^k:=(pow_le_pow_of_le_one hs.le hs1 hk).trans (pow_le_pow_left₀ hs.le hp k)
  have hsPow:0≤smin^h:=by positivity
  have hβn:β*n≤(smin^h/4)*m:=by
    have h1:=mul_le_mul_of_nonneg_right hβmax hn
    have h2:=mul_le_mul_of_nonneg_left hm (show 0≤smin^h/4 by positivity)
    nlinarith only [h1,h2]
  have hεm:ε*m≤(smin^h/2)*m:=mul_le_mul_of_nonneg_right hεmax hm0
  have hpm:(smin^h)*m≤pH^k*m:=mul_le_mul_of_nonneg_right hpow hm0
  have hnonneg:0≤smin^h*m:=mul_nonneg hsPow hm0
  nlinarith only [hβn,hεm,hpm,hnonneg]
end Oberwolfach
