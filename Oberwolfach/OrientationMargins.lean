module

public import Oberwolfach.AsymptoticMargins

@[expose] public section

/-! Uniform failure estimates and the numerical choices for balanced orientations. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Filter
open scoped BigOperators Topology
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem orientation_failure_sum_bound
    {V : Type*} [Fintype V] (G E : SimpleGraph V)
    (hdeg : ∀ v, 0 < G.degree v) {a α : ℝ}
    (hcommon : ∀ x y, x ≠ y → 2 * α * Fintype.card V ≤
      ((E.neighborFinset x ∩ E.neighborFinset y).card : ℝ)) :
    ((∑ x : V, 2 * Real.exp (-2 * a ^ 2 / G.degree x)) +
      (∑ p : {p : V × V // p.1 ≠ p.2},
        2 * Real.exp (-((E.neighborFinset p.1.1 ∩ E.neighborFinset p.1.2).card : ℝ) / 64))) ≤
      2 * Fintype.card V * Real.exp (-2 * a ^ 2 / Fintype.card V) +
      2 * (Fintype.card V : ℝ) ^ 2 * Real.exp (-α * Fintype.card V / 32) := by
  have hd : (∑ x : V, 2 * Real.exp (-2 * a ^ 2 / G.degree x)) ≤
      ∑ _x : V, 2 * Real.exp (-2 * a ^ 2 / Fintype.card V) := by
    apply Finset.sum_le_sum
    intro x _
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.exp_le_exp.mpr
    have hpos : (0 : ℝ) < G.degree x := by exact_mod_cast hdeg x
    have hle : (G.degree x : ℝ) ≤ Fintype.card V := by
      exact_mod_cast (G.degree_lt_card_verts x).le
    have hh := div_le_div_of_nonneg_left (show 0 ≤ (2 : ℝ) * a ^ 2 by positivity) hpos hle
    simpa only [neg_mul, neg_div] using neg_le_neg hh
  have hp : (∑ p : {p : V × V // p.1 ≠ p.2},
      2 * Real.exp (-((E.neighborFinset p.1.1 ∩ E.neighborFinset p.1.2).card : ℝ) / 64)) ≤
      ∑ _p : {p : V × V // p.1 ≠ p.2},
        2 * Real.exp (-α * Fintype.card V / 32) := by
    apply Finset.sum_le_sum
    intro p _
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.exp_le_exp.mpr
    linarith [hcommon p.1.1 p.1.2 p.2]
  have hcard : (Fintype.card {p : V × V // p.1 ≠ p.2} : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by
    have hh := Fintype.card_subtype_le (fun p : V × V => p.1 ≠ p.2)
    simpa only [Fintype.card_prod, Nat.cast_mul, pow_two] using (Nat.cast_le (α := ℝ)).mpr hh
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hd hp
  have hlast := mul_le_mul_of_nonneg_right hcard
    (show 0 ≤ 2 * Real.exp (-α * Fintype.card V / 32) by positivity)
  nlinarith

theorem threeFifths_tail_exponent {n : ℝ} (hn : 0 < n) :
    -2 * (n ^ (3 / 5 : ℝ)) ^ 2 / n = -2 * n ^ (1 / 5 : ℝ) := by
  have hp : (n ^ (3 / 5 : ℝ)) ^ 2 / n = n ^ (1 / 5 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le, ← Real.rpow_sub_one hn.ne']
    norm_num
  calc
    _ = -2 * ((n ^ (3 / 5 : ℝ)) ^ 2 / n) := by ring
    _ = _ := by rw [hp]

theorem eventually_orientation_failure_small_pow {α : ℝ} (hα : 0 < α) (q : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      2 * n * Real.exp (-2 * (n : ℝ) ^ (1 / 5 : ℝ)) +
      2 * (n : ℝ) ^ 2 * Real.exp (-α * n / 32) ≤ 1 / (n : ℝ) ^ q := by
  obtain ⟨N₁, h₁⟩ := eventually_stretchedExp_le_inv_pow 4 1
    (c := 2) (p := 1 / 5) (by norm_num) (by norm_num) q
  obtain ⟨N₂, h₂⟩ := eventually_stretchedExp_le_inv_pow 4 2
    (c := α / 32) (p := 1) (by positivity) (by norm_num) q
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have h1 := h₁ n (le_trans (le_max_left _ _) hn)
  have h2 := h₂ n (le_trans (le_max_right _ _) hn)
  simp only [Real.rpow_one, Real.rpow_two] at h1 h2
  have heq : -(α / 32) * (n : ℝ) = -α * n / 32 := by ring
  rw [heq] at h2
  linarith

theorem eventually_orientation_failure_small {α : ℝ} (hα : 0 < α) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      2 * n * Real.exp (-2 * (n : ℝ) ^ (1 / 5 : ℝ)) +
      2 * (n : ℝ) ^ 2 * Real.exp (-α * n / 32) ≤ 1 / (n : ℝ) ^ 10 :=
  eventually_orientation_failure_small_pow hα 10

theorem orientation_numeric_bounds {n α : ℝ} (hn : 1 ≤ n)
    (hb : 2 ≤ n ^ (4 / 5 : ℝ))
    (hsmall : 7 * n ^ (4 / 5 : ℝ) + 4 < 23 * α * n / 100) :
    0 < Nat.ceil (n ^ (4 / 5 : ℝ)) ∧
    n * n ^ (3 / 5 : ℝ) / Nat.ceil (n ^ (4 / 5 : ℝ)) +
        2 * n ^ (3 / 5 : ℝ) + 4 * Nat.ceil (n ^ (4 / 5 : ℝ)) + 2 * (α * n / 100) <
      (α / 4) * n ∧
    n ^ (3 / 5 : ℝ) + 2 * Nat.ceil (n ^ (4 / 5 : ℝ)) ≤ 4 * n ^ (4 / 5 : ℝ) := by
  have hnpos : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hLpos : 0 < Nat.ceil (n ^ (4 / 5 : ℝ)) := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hnpos _)
  have hLr : (0 : ℝ) < Nat.ceil (n ^ (4 / 5 : ℝ)) := by exact_mod_cast hLpos
  have ha : n ^ (3 / 5 : ℝ) ≤ n ^ (4 / 5 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hn (by norm_num)
  have hceil := Nat.le_ceil (n ^ (4 / 5 : ℝ))
  have hceil' := Nat.ceil_lt_add_one (Real.rpow_nonneg hnpos.le (4 / 5))
  have heq : n * n ^ (3 / 5 : ℝ) = (n ^ (4 / 5 : ℝ)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
    have hsum := Real.rpow_add hnpos 1 (3 / 5)
    norm_num only [Real.rpow_one] at hsum
    rw [← hsum]
    norm_num
  have hdiv : n * n ^ (3 / 5 : ℝ) / Nat.ceil (n ^ (4 / 5 : ℝ)) ≤ n ^ (4 / 5 : ℝ) := by
    apply (div_le_iff₀ hLr).mpr
    rw [heq]
    nlinarith [Real.rpow_nonneg hnpos.le (4 / 5)]
  exact ⟨hLpos, by nlinarith, by linarith⟩

theorem eventually_orientation_numeric {α : ℝ} (hα : 0 < α) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      0 < n ∧ 0 < Nat.ceil ((n : ℝ) ^ (4 / 5 : ℝ)) ∧
      (n : ℝ) * (n : ℝ) ^ (3 / 5 : ℝ) / Nat.ceil ((n : ℝ) ^ (4 / 5 : ℝ)) +
          2 * (n : ℝ) ^ (3 / 5 : ℝ) + 4 * Nat.ceil ((n : ℝ) ^ (4 / 5 : ℝ)) +
          2 * (α * n / 100) < (α / 4) * n ∧
      (n : ℝ) ^ (3 / 5 : ℝ) + 2 * Nat.ceil ((n : ℝ) ^ (4 / 5 : ℝ)) ≤
        4 * (n : ℝ) ^ (4 / 5 : ℝ) := by
  have h₁ := (tendsto_rpow_neg_atTop (y := 1 / 5) (by norm_num)).const_mul 7
  have h₂ := (tendsto_rpow_neg_atTop (y := 1) (by norm_num)).const_mul 4
  have hh := (h₁.add h₂).comp tendsto_natCast_atTop_atTop
  simp only [mul_zero, add_zero] at hh
  have hs : ∀ᶠ n : ℕ in atTop,
      7 * (n : ℝ) ^ (-(1 / 5 : ℝ)) + 4 * (n : ℝ) ^ (-(1 : ℝ)) < 23 * α / 100 :=
    hh.eventually (eventually_lt_nhds (by positivity))
  have ht := (tendsto_rpow_atTop (y := (4 / 5 : ℝ)) (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hb : ∀ᶠ n : ℕ in atTop, 2 ≤ (n : ℝ) ^ (4 / 5 : ℝ) := ht.eventually (eventually_ge_atTop 2)
  have hall : ∀ᶠ n : ℕ in atTop,
      0 < n ∧ 0 < Nat.ceil ((n : ℝ) ^ (4 / 5 : ℝ)) ∧
      (n : ℝ) * (n : ℝ) ^ (3 / 5 : ℝ) / Nat.ceil ((n : ℝ) ^ (4 / 5 : ℝ)) +
          2 * (n : ℝ) ^ (3 / 5 : ℝ) + 4 * Nat.ceil ((n : ℝ) ^ (4 / 5 : ℝ)) +
          2 * (α * n / 100) < (α / 4) * n ∧
      (n : ℝ) ^ (3 / 5 : ℝ) + 2 * Nat.ceil ((n : ℝ) ^ (4 / 5 : ℝ)) ≤
        4 * (n : ℝ) ^ (4 / 5 : ℝ) := by
    filter_upwards [hs, hb, eventually_ge_atTop 1] with n hs hb hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
    have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have heq : (n : ℝ) ^ (-(1 / 5 : ℝ)) = (n : ℝ) ^ (4 / 5 : ℝ) / n := by
      rw [← Real.rpow_sub_one hnpos.ne']
      norm_num
    have hsmall : 7 * (n : ℝ) ^ (4 / 5 : ℝ) + 4 < 23 * α * n / 100 := by
      rw [heq, Real.rpow_neg_one] at hs
      have hmul := mul_lt_mul_of_pos_right hs hnpos
      field_simp at hmul
      nlinarith
    exact ⟨by omega, orientation_numeric_bounds hnreal hb hsmall⟩
  exact eventually_atTop.mp hall

end Oberwolfach
