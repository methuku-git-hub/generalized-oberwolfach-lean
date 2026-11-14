module

public import Oberwolfach.ConfigurationFailureMargins

@[expose] public section
/-! Linear deviations make the reference balance, column and colour-degree
failure probabilities simultaneously small, uniformly for all hub counts. -/
set_option autoImplicit false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach

theorem ordinary_reference_concentration_tails_eventually_small
    (d:ℕ) (σ χ:ℝ) (hσ:0<σ) (hχ:0<χ):
    ∃N:ℕ,∀n:ℕ,N≤n→∀q:ℕ,0<q→q≤n→
      2*(n:ℝ)*Real.exp (-2*(σ*n)^2/n)+
      (n:ℝ)*(2*Real.exp (-2*(σ*n)^2/((4*(d:ℝ)+3)^2*q)))+
      4*(q:ℝ)*Real.exp (-2*(σ*n)^2/((4*(d:ℝ)+3)^2*n))+
      36*(n:ℝ)*Real.exp (-2*(σ*n)^2/n)≤χ :=by
  let A:ℝ:=(4*(d:ℝ)+3)^2
  have hA:0<A:=by dsimp [A];positivity
  obtain ⟨N1,hN1⟩:=linear_deviation_failure_eventually_small 1 1 σ (by norm_num) hσ 1 1
  obtain ⟨N2,hN2⟩:=linear_deviation_failure_eventually_small 1 A σ hA hσ 1 1
  obtain ⟨N3,hN3⟩:=linear_deviation_failure_eventually_small 2 A σ hA hσ 1 1
  obtain ⟨N4,hN4⟩:=linear_deviation_failure_eventually_small 18 1 σ (by norm_num) hσ 1 1
  obtain ⟨M,hM⟩:=exists_nat_gt (4/χ)
  refine ⟨max (max (max (max N1 N2) (max N3 N4)) M) 1,?_⟩
  intro n hn q hq hqn
  have hn0:0<(n:ℝ):=by exact_mod_cast (show 0<n by omega)
  have hq0:0<(q:ℝ):=by exact_mod_cast hq
  have hqnR:(q:ℝ)≤n:=by exact_mod_cast hqn
  have h1:=hN1 n (by omega) n n (by positivity) (by simp) hn0 (by simp)
  have h2:=hN2 n (by omega) n (A*q) (by positivity) (by simp) (by positivity) (mul_le_mul_of_nonneg_left hqnR hA.le)
  have h3:=hN3 n (by omega) (2*q) (A*n) (by positivity) (by nlinarith) (by positivity) (by linarith)
  have h4:=hN4 n (by omega) (18*n) n (by positivity) (by simp) hn0 (by simp)
  have hMle:(M:ℝ)≤n:=by exact_mod_cast (show M≤n by omega)
  have hfrac:4/(n:ℝ)≤χ:=by
    have hh:4/χ≤(n:ℝ):=hM.le.trans hMle
    have hh':4≤(n:ℝ)*χ:=(div_le_iff₀ hχ).mp hh
    exact (div_le_iff₀ hn0).2 (by nlinarith)
  dsimp [A] at h2 h3
  have heq1:2*(n:ℝ)*Real.exp (-2*(σ*n)^2/n)=(n:ℝ)*(2*Real.exp (-2*(σ*n)^2/n)):=by ring
  have heq3:4*(q:ℝ)*Real.exp (-2*(σ*n)^2/((4*(d:ℝ)+3)^2*n))=(2*(q:ℝ))*(2*Real.exp (-2*(σ*n)^2/((4*(d:ℝ)+3)^2*n))):=by ring
  have heq4:36*(n:ℝ)*Real.exp (-2*(σ*n)^2/n)=(18*(n:ℝ))*(2*Real.exp (-2*(σ*n)^2/n)):=by ring
  rw [heq1,heq3,heq4]
  norm_num at h1 h2 h3 h4 ⊢
  have hfrac' : 4 * (n:ℝ)⁻¹ ≤ χ := by simpa [div_eq_mul_inv] using hfrac
  linarith
end Oberwolfach
