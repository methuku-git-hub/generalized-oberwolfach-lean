module

public import Oberwolfach.OrientationMargins

@[expose] public section

/-! Uniform numerical choices for the protected partition. The protected
vertex fraction is alpha/100000 and is not chosen after the colour density. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Filter
open scoped Topology
noncomputable section
namespace Oberwolfach

theorem eventually_sublinear_le_linear {p ε : ℝ} (hp : p < 1) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (n : ℝ) ^ p ≤ ε * n := by
  have ht := (tendsto_rpow_neg_atTop (y := 1 - p) (by linarith)).comp
    tendsto_natCast_atTop_atTop
  have hs : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (-(1 - p)) < ε :=
    ht.eventually (eventually_lt_nhds hε)
  have hh : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ p ≤ ε * n := by
    filter_upwards [hs, eventually_ge_atTop 1] with n hs hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have heq : (n : ℝ) ^ (-(1 - p)) = (n : ℝ) ^ p / n := by
      rw [← Real.rpow_sub_one hnpos.ne']
      congr 1
      ring
    rw [heq] at hs
    exact ((div_lt_iff₀ hnpos).mp hs).le
  exact eventually_atTop.mp hh

theorem eventually_partition_margins {α r ξ qstar : ℝ}
    (hα : 0 < α) (hr : 0 < r) (hξ : 0 < ξ) (hqstar : 0 < qstar)
    (hqx : qstar ≤ ξ / 16) (hqh : qstar ≤ α * r / 2048)
    (hqr : qstar ≤ r / 64) (B : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      let t := (n : ℝ) ^ (3 / 5 : ℝ)
      let e := 5 * (n : ℝ) ^ (4 / 5 : ℝ)
      let q := Nat.floor (qstar * n)
      2 ≤ n ∧ e < q ∧
      (q : ℝ) ≤ r * n / 4 ∧
      2 * e / ((q : ℝ) - e) ≤ min (α / 32) (r / 512) ∧
      (q : ℝ) + e ≤ (α * r / 128) * n / 2 ∧
      4 * q + 2 * e ≤ ξ * n ∧
      t ≤ r * n / 32 ∧
      t + B + 4 * (n : ℝ) ^ (4 / 5 : ℝ) ≤ α * r * n / 256 ∧
      α / 100000 * n + B ≤ α * n / 100 := by
  let δ := min (α / 32) (r / 512)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  let η := min (qstar / 4) (min (δ * qstar / 16)
    (min (α * r / 2048) (min (ξ / 16) (r / 64))))
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨N₁, h₁⟩ := eventually_sublinear_le_linear (p := 4 / 5)
    (by norm_num) (ε := η / 5) (by positivity)
  obtain ⟨N₂, h₂⟩ := eventually_sublinear_le_linear (p := 0)
    (by norm_num) (ε := qstar / 4) (by positivity)
  obtain ⟨N₃, h₃⟩ := eventually_sublinear_le_linear (p := 4 / 5)
    (by norm_num) (ε := α * r / 2560) (by positivity)
  obtain ⟨N₄, h₄⟩ := eventually_sublinear_le_linear (p := 0)
    (by norm_num) (ε := min (α * r / (512 * (B + 1))) (α / (200 * (B + 1))))
    (by positivity)
  refine ⟨max 2 (max N₁ (max N₂ (max N₃ N₄))), fun n hn => ?_⟩
  dsimp only
  have hn2 : 2 ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hn0 := hnpos.le
  have h1 := h₁ n (by omega)
  have h2 := h₂ n (by omega)
  have h3 := h₃ n (by omega)
  have h4 := h₄ n (by omega)
  simp only [Real.rpow_zero] at h2 h4
  have ha : (n : ℝ) ^ (3 / 5 : ℝ) ≤ (n : ℝ) ^ (4 / 5 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  have heη : 5 * (n : ℝ) ^ (4 / 5 : ℝ) ≤ η * n := by linarith
  have hηq : η ≤ qstar / 4 := min_le_left _ _
  have hηδ : η ≤ δ * qstar / 16 := (min_le_right _ _).trans (min_le_left _ _)
  have hηh : η ≤ α * r / 2048 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hηx : η ≤ ξ / 16 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hηr : η ≤ r / 64 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have heq := heη.trans (mul_le_mul_of_nonneg_right hηq hn0)
  have heδ := heη.trans (mul_le_mul_of_nonneg_right hηδ hn0)
  have heh := heη.trans (mul_le_mul_of_nonneg_right hηh hn0)
  have hex := heη.trans (mul_le_mul_of_nonneg_right hηx hn0)
  have her := heη.trans (mul_le_mul_of_nonneg_right hηr hn0)
  have hfloor := Nat.floor_le (show 0 ≤ qstar * (n : ℝ) by positivity)
  have hfloor' := Nat.lt_floor_add_one (qstar * (n : ℝ))
  have hqpos : 5 * (n : ℝ) ^ (4 / 5 : ℝ) < Nat.floor (qstar * n) := by
    nlinarith
  have hqgap : qstar * n / 2 ≤ (Nat.floor (qstar * n) : ℝ) - 5 * (n : ℝ) ^ (4 / 5 : ℝ) := by
    linarith
  have hratio : 2 * (5 * (n : ℝ) ^ (4 / 5 : ℝ)) /
      ((Nat.floor (qstar * n) : ℝ) - 5 * (n : ℝ) ^ (4 / 5 : ℝ)) ≤ δ := by
    apply (div_le_iff₀ (by linarith : (0 : ℝ) < Nat.floor (qstar * n) - 5 * (n : ℝ) ^ (4 / 5 : ℝ))).mpr
    have hm := mul_le_mul_of_nonneg_left hqgap hδ.le
    nlinarith [mul_pos hδ (mul_pos hqstar hnpos)]
  have hb₁ : (B : ℝ) ≤ α * r * n / 512 := by
    have hsmall := (min_le_left (α * r / (512 * (B + 1))) (α / (200 * (B + 1))))
    have hh := h4.trans (mul_le_mul_of_nonneg_right hsmall hn0)
    have hm := mul_le_mul_of_nonneg_right hh (show (0 : ℝ) ≤ 512 * (B + 1) by positivity)
    field_simp at hm
    nlinarith
  have hb₂ : (B : ℝ) ≤ α * n / 200 := by
    have hsmall := (min_le_right (α * r / (512 * (B + 1))) (α / (200 * (B + 1))))
    have hh := h4.trans (mul_le_mul_of_nonneg_right hsmall hn0)
    have hm := mul_le_mul_of_nonneg_right hh (show (0 : ℝ) ≤ 200 * (B + 1) by positivity)
    field_simp at hm
    nlinarith
  have hqxn := mul_le_mul_of_nonneg_right hqx hn0
  have hqhn := mul_le_mul_of_nonneg_right hqh hn0
  have hqrn := mul_le_mul_of_nonneg_right hqr hn0
  refine ⟨hn2, hqpos, ?_, hratio, ?_, ?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · nlinarith [mul_pos hα hnpos]

end Oberwolfach
