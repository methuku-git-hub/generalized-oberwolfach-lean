module

public import Oberwolfach.ProtectedSets

@[expose] public section
/-! A uniform failure allowance for all retained classes and the partition
failure, with a threshold chosen after the cutoff. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem preparation_class_failure_budget (K:ℕ):
    ∃χ:ℝ,0<χ ∧ χ<1 ∧ ∃N:ℕ,∀n≥N,∀k≤K+1,
      1/(n:ℝ)^10+(k:ℝ)*(χ+1/(n:ℝ)^10)<1 :=by
  let χ:ℝ:=1/(100*((K:ℝ)+2))
  have hK:0<(K:ℝ)+2:=by positivity
  have hχ:0<χ:=by dsimp [χ];positivity
  have hχ1:χ<1:=by
    dsimp [χ]
    rw [div_lt_one (by positivity)]
    have : (0:ℝ)≤K:=Nat.cast_nonneg K
    linarith
  refine ⟨χ,hχ,hχ1,2*(K+2),?_⟩
  intro n hn k hk
  have hnR:(2:ℝ)*((K:ℝ)+2)≤n:=by exact_mod_cast hn
  have hkR:(k:ℝ)≤K+1:=by exact_mod_cast hk
  have hn1:(1:ℝ)≤n:=by linarith
  have hpow1:1≤(n:ℝ)^9:=one_le_pow₀ hn1
  have hpow:(n:ℝ)≤(n:ℝ)^10:=by rw [pow_succ];nlinarith
  have hpow2:2*((K:ℝ)+2)≤(n:ℝ)^10:=hnR.trans hpow
  have hfrac:1/(n:ℝ)^10≤1/(2*((K:ℝ)+2)):=
    one_div_le_one_div_of_le (by positivity) hpow2
  have hk0:(0:ℝ)≤k:=Nat.cast_nonneg k
  have hf0:0≤1/(n:ℝ)^10:=by positivity
  have hc:(k:ℝ)*χ≤1/100:=by
    dsimp [χ]
    have hle:(k:ℝ)≤(K:ℝ)+2:=by linarith
    have hp:0<(K:ℝ)+2:=by positivity
    apply (le_div_iff₀ (by norm_num:(0:ℝ)<100)).2
    field_simp
    nlinarith
  have hf:(k+1:ℝ)*(1/(n:ℝ)^10)≤1/2:=by
    have hmul:=mul_le_mul_of_nonneg_left hfrac (by positivity:(0:ℝ)≤(k:ℝ)+1)
    have hdiv:((k:ℝ)+1)/(2*((K:ℝ)+2))≤1/2:=by
      apply (div_le_iff₀ (by positivity:0<2*((K:ℝ)+2))).2
      linarith
    have hmul':((k:ℝ)+1)*(1/(n:ℝ)^10)≤((k:ℝ)+1)/(2*((K:ℝ)+2)):=by
      simpa [div_eq_mul_inv] using hmul
    exact hmul'.trans hdiv
  nlinarith
end Oberwolfach
