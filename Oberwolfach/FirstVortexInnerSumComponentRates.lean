module

public import Mathlib.Tactic

@[expose] public section
/-! Component estimates for the local change bounds with a summed inner
error and independently fixed global matching tolerance. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_inner_sum_component_rates
    (n d:ℕ) (t s θ a γ ξPart boundary κ Δ ζret ηBalance:ℝ)
    (ht:0≤t) (hs:0≤s) (hθ:θ≤s) (ha:a≤s) (hγ:γ≤s) (hξ:ξPart≤s)
    (hboundary:boundary≤s*n) (hκ:κ≤s) (hΔ:Δ≤s) (hret:ζret≤s) (hbal:ηBalance≤s)
    (hfixed:((6*d+2:ℕ):ℝ)≤s*n) (hunit:1≤s*n) (hrate:16*s≤t)
    (hpow:(n:ℝ)^(3/5:ℝ)≤(t/4)*n):
    2*θ+2*max a (4*γ)+2*ξPart≤t ∧
    boundary+2*(max a γ*n)+((6*d+2:ℕ):ℝ)+(κ*n+1)≤t*n ∧
    (n:ℝ)^(3/5:ℝ)+2*Δ*n+2*(6*d+2:ℕ)≤t*n ∧
    ζret≤t ∧ ηBalance≤t :=by
  have hn:(0:ℝ)≤n:=Nat.cast_nonneg _
  have h4:4*γ≤4*s:=by linarith
  have ha4:a≤4*s:=by linarith
  have hmax:max a (4*γ)≤4*s:=max_le ha4 h4
  have hmax2:max a γ≤s:=max_le ha hγ
  have hmaxn:=mul_le_mul_of_nonneg_right hmax2 hn
  have hκn:=mul_le_mul_of_nonneg_right hκ hn
  have hΔn:=mul_le_mul_of_nonneg_right hΔ hn
  have hraten:=mul_le_mul_of_nonneg_right hrate hn
  constructor
  · linarith
  constructor
  · nlinarith
  constructor
  · push_cast at *
    nlinarith
  constructor <;> linarith
end Oberwolfach
