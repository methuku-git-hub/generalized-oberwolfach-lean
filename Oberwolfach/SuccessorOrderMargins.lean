module

public import Oberwolfach.PartitionFailureScale
public import Oberwolfach.SuccessorWeightScale

@[expose] public section

/-! Uniform order thresholds for the equal-cell partition, with all
sampling and rounding errors bounded by prescribed positive constants. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem eventually_reciprocal_small (t : ℝ) (ht : 0 < t) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 0 < n ∧ 1 / (n : ℝ) ≤ t := by
  refine ⟨max 1 ⌈1/t⌉₊,?_⟩
  intro n hn
  have hnpos : 0 < n := by omega
  have hnr : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hceil : (⌈1/t⌉₊ : ℝ) ≤ n := by exact_mod_cast ((le_max_right _ _).trans hn)
  have htN : 1/t ≤ (n : ℝ) := (Nat.le_ceil _).trans hceil
  refine ⟨hnpos,?_⟩
  apply (div_le_iff₀ hnr).mpr
  have hh := (div_le_iff₀ ht).mp htN
  nlinarith

theorem successor_pair_probability_lower {m n : ℝ} (hm : 0 ≤ m) (hn : 1 < n) :
    (m/n)^2 ≤ successorPairProbability m n := by
  rw [div_pow]
  unfold successorPairProbability
  apply div_le_div_of_nonneg_left (sq_nonneg m) (by positivity)
  nlinarith

theorem successor_order_margins (c m₀ : ℕ) (hc : 0 < c)
    (η ε ξ : ℝ) (hη : 0 < η) (hε : 0 < ε) (hξ : 0 < ξ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      2 ≤ n ∧ 0 < n/c ∧ m₀ ≤ n/c ∧ n ≤ 2*c*(n/c) ∧
      1 / ((n/c : ℕ) : ℝ) ≤ ξ ∧ 2 / (n : ℝ) ≤ ξ ∧
      partitionFailure c η n ≤ ε * successorPairProbability (n/c : ℕ) n ∧
      partitionFailure c η n ≤ (1/2) * (((n/c : ℕ) : ℝ) / n)^c := by
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast hc
  let t := min (ξ/(2*c)) (min (ε*(1/(2*c))^2) ((1/2)*(1/(2*c))^c))
  have ht : 0 < t := by dsimp [t]; positivity
  obtain ⟨N₁,hN₁⟩ := partition_failure_eventually_small c hc η hη
  obtain ⟨N₂,hN₂⟩ := eventually_reciprocal_small t ht
  refine ⟨max N₁ (max N₂ (max 2 (c * max m₀ 1))),?_⟩
  intro n hn
  have hn₁ : N₁ ≤ n := (le_max_left _ _).trans hn
  have hn₂ : N₂ ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hlarge : max 2 (c * max m₀ 1) ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hn2 : 2 ≤ n := (le_max_left _ _).trans hlarge
  have hnr : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hn0 : (0 : ℝ) < n := by linarith
  obtain ⟨hmpos,hscale,hfail⟩ := hN₁ n hn₁
  have hmR : (0 : ℝ) < (n/c : ℕ) := by exact_mod_cast hmpos
  have hscaleR : (n : ℝ) ≤ 2*c*(n/c : ℕ) := by exact_mod_cast hscale
  have hrecip := (hN₂ n hn₂).2
  have hm₀ : m₀ ≤ n/c := (Nat.le_div_iff_mul_le hc).mpr (by
    have hh := (le_max_right _ _).trans hlarge
    nlinarith [le_max_left m₀ 1])
  have hξN : (2*c : ℝ) / n ≤ ξ := by
    have hh := hrecip.trans (min_le_left _ _)
    have hhh := mul_le_mul_of_nonneg_left hh (show (0 : ℝ) ≤ 2*c by positivity)
    have he : (2*c : ℝ) * (ξ/(2*c)) = ξ := by field_simp
    rw [he] at hhh
    simpa only [mul_one_div] using hhh
  have hmξ : (1 : ℝ) / (n/c : ℕ) ≤ ξ := by
    apply le_trans _ hξN
    apply (le_div_iff₀ hn0).mpr
    have hh : (n : ℝ) / (n/c : ℕ) ≤ 2*c := (div_le_iff₀ hmR).mpr hscaleR
    convert hh using 1 <;> ring
  have hnξ : (2 : ℝ) / n ≤ ξ :=
    (div_le_div_of_nonneg_right (by linarith : (2 : ℝ) ≤ 2*c) hn0.le).trans hξN
  have hratio : (1 : ℝ)/(2*c) ≤ ((n/c : ℕ) : ℝ)/n := by
    apply (le_div_iff₀ hn0).mpr
    have hh : (n : ℝ)/(2*c) ≤ (n/c : ℕ) := (div_le_iff₀ (by positivity)).mpr (by nlinarith)
    convert hh using 1 <;> ring
  have hp : ((1 : ℝ)/(2*c))^2 ≤ successorPairProbability (n/c : ℕ) n :=
    (pow_le_pow_left₀ (by positivity) hratio 2).trans (successor_pair_probability_lower hmR.le hnr)
  have htuple := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1/(2*c)) hratio c
  refine ⟨hn2,hmpos,hm₀,hscale,hmξ,hnξ,?_,?_⟩
  · exact (hfail.trans (hrecip.trans ((min_le_right _ _).trans (min_le_left _ _)))).trans
      (mul_le_mul_of_nonneg_left hp hε.le)
  · exact (hfail.trans (hrecip.trans ((min_le_right _ _).trans (min_le_right _ _)))).trans
      (mul_le_mul_of_nonneg_left htuple (by norm_num))

end Oberwolfach
