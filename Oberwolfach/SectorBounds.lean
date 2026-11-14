module

public import Mathlib.Tactic

@[expose] public section

/-! Uniform power bounds for the cancelled sector formula. Empty products
are included, so the four-cycle case needs no separate convention. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem scaled_product_ratio_identity (a b : ℕ) (r c m n : ℝ)
    (hc : c ≠ 0) (hm : m ≠ 0) (hn : n ≠ 0) :
    (r / n) ^ a / (c * n * (m * n) ^ b) =
      (r ^ a / (c * m ^ b)) / n ^ (a + b + 1) := by
  simp only [div_pow, mul_pow, pow_add, pow_one]
  field_simp

theorem product_ratio_bounds {I J : Type*}
    (D : Finset I) (T : Finset J) (R : I → ℝ) (m : J → ℝ)
    (n rlo rhi clo chi mlo mhi C : ℝ)
    (hn : 0 < n) (hrlo : 0 < rlo) (hrhi : 0 < rhi)
    (hclo : 0 < clo) (hchi : 0 < chi) (hmlo : 0 < mlo) (hmhi : 0 < mhi)
    (hR : ∀ i ∈ D, rlo / n ≤ R i ∧ R i ≤ rhi / n)
    (hm : ∀ j ∈ T, mlo * n ≤ m j ∧ m j ≤ mhi * n)
    (hC : clo * n ≤ C ∧ C ≤ chi * n) :
    (rlo ^ D.card / (chi * mhi ^ T.card)) / n ^ (D.card + T.card + 1) ≤
        (∏ i ∈ D, R i) / (C * ∏ j ∈ T, m j) ∧
    (∏ i ∈ D, R i) / (C * ∏ j ∈ T, m j) ≤
      (rhi ^ D.card / (clo * mlo ^ T.card)) / n ^ (D.card + T.card + 1) := by
  have hR0 (i : I) (hi : i ∈ D) : 0 ≤ R i :=
    (div_pos hrlo hn).le.trans (hR i hi).1
  have hm0 (j : J) (hj : j ∈ T) : 0 < m j :=
    lt_of_lt_of_le (mul_pos hmlo hn) (hm j hj).1
  have hC0 : 0 < C := lt_of_lt_of_le (mul_pos hclo hn) hC.1
  have hRlo : (rlo / n) ^ D.card ≤ ∏ i ∈ D, R i := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod₀ (fun _ _ => (div_pos hrlo hn).le) (fun i hi => (hR i hi).1)
  have hRhi : (∏ i ∈ D, R i) ≤ (rhi / n) ^ D.card := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod₀ hR0 (fun i hi => (hR i hi).2)
  have hmlo' : (mlo * n) ^ T.card ≤ ∏ j ∈ T, m j := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod₀ (fun _ _ => (mul_pos hmlo hn).le) (fun j hj => (hm j hj).1)
  have hmhi' : (∏ j ∈ T, m j) ≤ (mhi * n) ^ T.card := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod₀ (fun j hj => (hm0 j hj).le) (fun j hj => (hm j hj).2)
  have hdenlo : clo * n * (mlo * n) ^ T.card ≤ C * ∏ j ∈ T, m j :=
    mul_le_mul hC.1 hmlo' (pow_pos (mul_pos hmlo hn) _).le hC0.le
  have hdenhi : C * (∏ j ∈ T, m j) ≤ chi * n * (mhi * n) ^ T.card :=
    mul_le_mul hC.2 hmhi' (Finset.prod_pos hm0).le (mul_pos hchi hn).le
  have hden0 : 0 < C * ∏ j ∈ T, m j := mul_pos hC0 (Finset.prod_pos hm0)
  constructor
  · rw [← scaled_product_ratio_identity D.card T.card rlo chi mhi n hchi.ne' hmhi.ne' hn.ne']
    exact div_le_div₀ (Finset.prod_nonneg hR0) hRlo hden0 hdenhi
  · rw [← scaled_product_ratio_identity D.card T.card rhi clo mlo n hclo.ne' hmlo.ne' hn.ne']
    exact div_le_div₀ (pow_pos (div_pos hrhi hn) _).le hRhi
      (mul_pos (mul_pos hclo hn) (pow_pos (mul_pos hmlo hn) _)) hdenlo

end Oberwolfach
