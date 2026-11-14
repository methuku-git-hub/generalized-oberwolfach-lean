module

public import Oberwolfach.AsymptoticMargins
public import Mathlib.Data.Nat.Choose.Bounds

@[expose] public section

/-! Uniform binomial union bounds when the deletion probability tends to
zero polynomially. The order threshold is independent of the tested set size. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Filter
noncomputable section
namespace Oberwolfach

theorem binomial_tail_le_geometric (M k : ℕ) (p a : ℝ)
    (hp : 0≤p) (hp1 : p≤1) (ha : 0≤a) (hk : a*M≤(k:ℝ)) :
    (M.choose k:ℝ)*p^k≤(2*p^a)^M := by
  have hc : (M.choose k:ℝ)≤(2:ℝ)^M := by exact_mod_cast Nat.choose_le_two_pow M k
  have he : p^k≤(p^a)^M := by
    rw [← Real.rpow_natCast,← Real.rpow_natCast,← Real.rpow_mul hp]
    exact Real.rpow_le_rpow_of_exponent_ge' hp hp1 (by positivity) hk
  calc
    _ ≤ (2:ℝ)^M*((p^a)^M) := mul_le_mul hc he (by positivity) (by positivity)
    _ = _ := (mul_pow _ _ _).symm

theorem eventually_binomial_deletion_tail (K a b : ℝ) (hK : 0≤K) (ha : 0<a) (hb : 0<b) :
    ∃ N : ℕ,1≤N ∧ ∀ n : ℕ,N≤n → ∀ M k : ℕ,∀ p : ℝ,
      0≤p → p≤K*(n:ℝ)^(-b) → a*M≤(k:ℝ) →
      (M.choose k:ℝ)*p^k≤(n:ℝ)^(-(a*b/2)*M) := by
  let c := a*b/2
  have hc : 0<c := by dsimp [c];positivity
  have hlim₁ := ((tendsto_rpow_neg_atTop hb).const_mul K).comp tendsto_natCast_atTop_atTop
  have hlim₂ := ((tendsto_rpow_neg_atTop hc).const_mul (2*K^a)).comp tendsto_natCast_atTop_atTop
  simp only [mul_zero] at hlim₁ hlim₂
  obtain ⟨N₁,hN₁⟩ := eventually_atTop.mp (hlim₁.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1)))
  obtain ⟨N₂,hN₂⟩ := eventually_atTop.mp (hlim₂.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1)))
  refine ⟨max 1 (max N₁ N₂),le_max_left _ _,?_⟩
  intro n hn M k p hp hrate hk
  have hnpos : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hsmall₁ : K*(n:ℝ)^(-b)≤1 := (hN₁ n (by omega)).le
  have hsmall₂ : (2*K^a)*(n:ℝ)^(-c)≤1 := (hN₂ n (by omega)).le
  have hbase : 2*p^a≤(n:ℝ)^(-c) := by
    have heq : 2*(K*(n:ℝ)^(-b))^a=((2*K^a)*(n:ℝ)^(-c))*(n:ℝ)^(-c) := by
      rw [Real.mul_rpow hK (by positivity),← Real.rpow_mul hnpos.le]
      have he : -b*a = -c + -c := by dsimp [c];ring
      rw [he,Real.rpow_add hnpos]
      ring
    calc
      _ ≤ 2*(K*(n:ℝ)^(-b))^a := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hp hrate ha.le) (by norm_num)
      _ = _ := heq
      _ ≤ 1*(n:ℝ)^(-c) := mul_le_mul_of_nonneg_right hsmall₂ (by positivity)
      _ = _ := one_mul _
  calc
    _ ≤ (2*p^a)^M := binomial_tail_le_geometric M k p a hp (hrate.trans hsmall₁) ha.le hk
    _ ≤ ((n:ℝ)^(-c))^M := pow_le_pow_left₀ (by positivity) hbase M
    _ = (n:ℝ)^(-(a*b/2)*M) := by rw [← Real.rpow_natCast,← Real.rpow_mul hnpos.le]

end Oberwolfach
