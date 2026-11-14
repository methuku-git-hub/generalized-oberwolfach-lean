module

public import Oberwolfach.LongPaddedLengthSum

@[expose] public section
/-! The original matching tolerance makes the ordinary-cycle mass error
smaller than θn. -/
set_option autoImplicit false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem long_ordinary_mass_error_le_theta_div_100
    (K n:ℕ) (hK:3≤K) (θ lam eps:ℝ)
    (hθ:0≤θ) (hθmax:θ≤1/100) (hlam:0≤lam) (hlamθ:lam≤θ) (heps:0≤eps)
    (hepsAssign:3*eps≤lam*(θ/(100*(K:ℝ)^2))):
    ((max (3*eps) 0)*(n:ℝ))*(∑i:Fin K,((longPaddedSeedExponent i+2:ℕ):ℝ))≤(θ/100)*n:=by
  have hK0:(0:ℝ)<K:=by exact_mod_cast (show 0<K by omega)
  have hn:(0:ℝ)≤n:=by positivity
  have hmax:max (3*eps) 0=3*eps:=max_eq_left (by positivity)
  rw [hmax]
  have hlen:=long_padded_length_sum_bound K
  have hmaxK:(max 3 K:ℕ)=K:=max_eq_right hK
  rw [hmaxK] at hlen
  have hlen':(∑i:Fin K,((longPaddedSeedExponent i+2:ℕ):ℝ))≤(K:ℝ)^2:=by nlinarith
  have hlen0:0≤(∑i:Fin K,((longPaddedSeedExponent i+2:ℕ):ℝ)):=by positivity
  have hbound:=mul_le_mul_of_nonneg_right hepsAssign (sq_nonneg (K:ℝ))
  have hKne:(K:ℝ)≠0:=ne_of_gt hK0
  have heq:lam*(θ/(100*(K:ℝ)^2))*(K:ℝ)^2=lam*θ/100:=by field_simp
  rw [heq] at hbound
  have hlam1:lam≤1:=by linarith
  have hθprod:lam*θ≤θ:=by nlinarith [mul_nonneg (sub_nonneg.mpr hlam1) hθ]
  have hscale:3*eps*(K:ℝ)^2≤θ/100:=by nlinarith
  have hh:=mul_le_mul_of_nonneg_left hlen' (show 0≤(3*eps)*(n:ℝ) by positivity)
  have hh':(3*eps*(K:ℝ)^2)*(n:ℝ)≤(θ/100)*n:=mul_le_mul_of_nonneg_right hscale hn
  nlinarith
end Oberwolfach
