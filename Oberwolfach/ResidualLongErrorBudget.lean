module

public import Oberwolfach.LongAssignedIntervalSumBounds
public import Oberwolfach.ApproximateSublinearMargin

@[expose] public section
/-! Choose an order threshold and a retention tolerance so the explicit
full-selection errors cost at most four θn. -/
set_option autoImplicit false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach

theorem residual_long_error_budget
    (m d:ℕ) (hm:0<m) (hd:1≤d) (θ:ℝ) (hθ:0<θ)
    (hcut:1/(((m:ℝ)+1)*(d:ℝ))≤θ):
    ∃ζ:ℝ,0<ζ ∧ ∃N:ℕ,∀n:ℕ,N≤n→∀q errOrd:ℝ,
      q≤1/((m:ℝ)+1)→errOrd≤θ*n→
      (n:ℝ)*q/d+(((m+1)*d-1:ℕ):ℝ)*(2*((n:ℝ)^(3/4:ℝ)/d)+ζ*n)+errOrd≤4*θ*n:=by
  let c:ℝ:=(m:ℝ)+1
  let ζ:ℝ:=θ/(c*(d:ℝ))
  have hc:0<c:=by dsimp [c];positivity
  have hdR:(0:ℝ)<d:=by exact_mod_cast (show 0<d by omega)
  have hζ:0<ζ:=by dsimp [ζ];positivity
  obtain ⟨N,hN⟩:=eventually_three_quarters_and_constant_le_linear (θ/(2*c)) 0 (by positivity)
  refine ⟨ζ,hζ,N,?_⟩
  intro n hn q errOrd hq herr
  have hn0:(0:ℝ)≤n:=by positivity
  have hp:(0:ℝ)≤(n:ℝ)^(3/4:ℝ):=by positivity
  have hcdNat:1≤(m+1)*d:=by nlinarith
  have hcoef:(((m+1)*d-1:ℕ):ℝ)=c*(d:ℝ)-1:=by rw [Nat.cast_sub hcdNat];dsimp [c];push_cast;ring
  have hcoeff0:0≤(((m+1)*d-1:ℕ):ℝ):=by positivity
  have hcoeff:(((m+1)*d-1:ℕ):ℝ)≤c*(d:ℝ):=by rw [hcoef];linarith
  have hq1: (n:ℝ)*q/d≤θ*n:=by
    have hh:=mul_le_mul_of_nonneg_left hq hn0
    have hh':(n:ℝ)*q/d≤(n:ℝ)*(1/c)/d:=div_le_div_of_nonneg_right hh hdR.le
    have hcut':(1/c)/(d:ℝ)≤θ:=by dsimp [c] at *;convert hcut using 1 <;> field_simp
    have hmul:=mul_le_mul_of_nonneg_right hcut' hn0
    calc
      _ ≤ (n:ℝ)*(1/c)/d:=hh'
      _ = ((1/c)/(d:ℝ))*n:=by ring
      _ ≤ _:=hmul
  have hsub:(((m+1)*d-1:ℕ):ℝ)*(2*((n:ℝ)^(3/4:ℝ)/d))≤θ*n:=by
    have hp2:0≤2*((n:ℝ)^(3/4:ℝ)/d):=by positivity
    have hh:=mul_le_mul_of_nonneg_right hcoeff hp2
    have heq:c*(d:ℝ)*(2*((n:ℝ)^(3/4:ℝ)/d))=2*c*(n:ℝ)^(3/4:ℝ):=by field_simp
    rw [heq] at hh
    have hpow:=hN n hn
    have hh' := mul_le_mul_of_nonneg_left hpow (show 0≤2*c by positivity)
    have heq':(2*c)*(θ/(2*c)*n)=θ*n:=by field_simp
    nlinarith [heq']
  have hret:(((m+1)*d-1:ℕ):ℝ)*(ζ*n)≤θ*n:=by
    have hh:=mul_le_mul_of_nonneg_right hcoeff (show 0≤ζ*n by positivity)
    have heq:c*(d:ℝ)*(ζ*n)=θ*n:=by dsimp [ζ];field_simp
    nlinarith
  nlinarith
end Oberwolfach
