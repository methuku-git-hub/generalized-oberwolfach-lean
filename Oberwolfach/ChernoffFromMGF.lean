module

public import Oberwolfach.FiniteExponential
public import Oberwolfach.EntropyBounds

@[expose] public section

/-! Chernoff tails from the Poisson exponential-moment bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem finiteLaw_poisson_mgf_upper_tail
    {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (X : Ω → ℝ)
    {a : ℝ} (ha : 0 ≤ a)
    (hmgf : ∀ s, μ.expectation (fun ω => Real.exp (s * X ω)) ≤
      Real.exp (a * (Real.exp s - 1)))
    {ε : ℝ} (he : 0 ≤ ε) (he1 : ε ≤ 1) :
    μ.probability (fun ω => (1 + ε) * a ≤ X ω) ≤ Real.exp (-ε ^ 2 * a / 3) := by
  have hpos : 0 < 1 + ε := by linarith
  have hlog : 0 ≤ Real.log (1 + ε) := Real.log_nonneg (by linarith)
  calc
    _ ≤ Real.exp (-Real.log (1 + ε) * ((1 + ε) * a)) *
        μ.expectation (fun ω => Real.exp (Real.log (1 + ε) * X ω)) :=
      finiteLaw_exponential_markov μ X _ hlog
    _ ≤ Real.exp (-Real.log (1 + ε) * ((1 + ε) * a)) *
        Real.exp (a * (Real.exp (Real.log (1 + ε)) - 1)) :=
      mul_le_mul_of_nonneg_left (hmgf _) (Real.exp_pos _).le
    _ = Real.exp (-a * ((1 + ε) * Real.log (1 + ε) - ε)) := by
      rw [← Real.exp_add, Real.exp_log hpos]
      congr 1
      ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_left (chernoff_upper_entropy he he1) ha
      nlinarith

theorem finiteLaw_poisson_mgf_lower_tail
    {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (X : Ω → ℝ)
    {a : ℝ} (ha : 0 ≤ a)
    (hmgf : ∀ s, μ.expectation (fun ω => Real.exp (s * X ω)) ≤
      Real.exp (a * (Real.exp s - 1)))
    {ε : ℝ} (he : 0 ≤ ε) :
    μ.probability (fun ω => X ω ≤ (1 - ε) * a) ≤ Real.exp (-ε ^ 2 * a / 2) := by
  have hm : μ.expectation (fun ω => Real.exp (ε * (-X ω))) ≤
      Real.exp (a * (Real.exp (-ε) - 1)) := by
    simpa only [mul_neg, neg_mul] using hmgf (-ε)
  have ht := finiteLaw_exponential_markov μ (fun ω => -X ω) (-((1 - ε) * a)) he
  have hev : (fun ω => -((1 - ε) * a) ≤ -X ω) = (fun ω => X ω ≤ (1 - ε) * a) := by
    funext ω
    exact propext neg_le_neg_iff
  rw [hev] at ht
  calc
    _ ≤ Real.exp (-ε * (-((1 - ε) * a))) * μ.expectation (fun ω => Real.exp (ε * (-X ω))) := ht
    _ ≤ Real.exp (-ε * (-((1 - ε) * a))) * Real.exp (a * (Real.exp (-ε) - 1)) :=
      mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le
    _ = Real.exp (a * (Real.exp (-ε) - 1 + ε - ε ^ 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_left (exp_neg_upper_quadratic he) ha
      nlinarith

theorem finiteLaw_poisson_mgf_absolute_tail
    {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (X : Ω → ℝ)
    {a : ℝ} (ha : 0 ≤ a)
    (hmgf : ∀ s, μ.expectation (fun ω => Real.exp (s * X ω)) ≤
      Real.exp (a * (Real.exp s - 1)))
    {ε : ℝ} (he : 0 ≤ ε) (he1 : ε ≤ 1) :
    μ.probability (fun ω => ε * a ≤ |X ω - a|) ≤ 2 * Real.exp (-ε ^ 2 * a / 3) := by
  classical
  let A (b : Bool) (ω : Ω) := if b then (1 + ε) * a ≤ X ω else X ω ≤ (1 - ε) * a
  have hev : (fun ω => ε * a ≤ |X ω - a|) =
      (fun ω => ∃ b ∈ (Finset.univ : Finset Bool), A b ω) := by
    funext ω
    apply propext
    simp only [Finset.mem_univ, true_and, Bool.exists_bool, A, Bool.false_eq_true, ite_false, ite_true, le_abs]
    constructor
    · rintro (h | h) <;> [right; left] <;> linarith
    · rintro (h | h) <;> [right; left] <;> linarith
  rw [hev]
  have hu := finiteLaw_poisson_mgf_upper_tail μ X ha hmgf he he1
  have hl := finiteLaw_poisson_mgf_lower_tail μ X ha hmgf he
  have hcomp : Real.exp (-ε ^ 2 * a / 2) ≤ Real.exp (-ε ^ 2 * a / 3) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (sq_nonneg ε) ha]
  have hsum := finiteLaw_union_bound μ Finset.univ A
  simp only [Fintype.sum_bool, A, Bool.false_eq_true, ite_false, ite_true] at hsum
  linarith

theorem finiteLaw_poisson_mgf_large_tail
    {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (X : Ω → ℝ)
    {a : ℝ} (ha : 0 < a)
    (hmgf : ∀ s, μ.expectation (fun ω => Real.exp (s * X ω)) ≤
      Real.exp (a * (Real.exp s - 1)))
    {t : ℝ} (ht : a ≤ t) :
    μ.probability (fun ω => t ≤ X ω) ≤ (Real.exp 1 * a / t) ^ t := by
  have htpos : 0 < t := lt_of_lt_of_le ha ht
  have hquot : 0 < t / a := div_pos htpos ha
  have hlog : 0 ≤ Real.log (t / a) :=
    Real.log_nonneg ((one_le_div ha).mpr ht)
  calc
    _ ≤ Real.exp (-Real.log (t / a) * t) *
        μ.expectation (fun ω => Real.exp (Real.log (t / a) * X ω)) :=
      finiteLaw_exponential_markov μ X t hlog
    _ ≤ Real.exp (-Real.log (t / a) * t) *
        Real.exp (a * (Real.exp (Real.log (t / a)) - 1)) :=
      mul_le_mul_of_nonneg_left (hmgf _) (Real.exp_pos _).le
    _ = Real.exp (t * (1 + Real.log a - Real.log t) - a) := by
      rw [← Real.exp_add, Real.exp_log hquot, Real.log_div htpos.ne' ha.ne']
      congr 1
      field_simp
      ring
    _ ≤ Real.exp (t * (1 + Real.log a - Real.log t)) :=
      Real.exp_le_exp.mpr (sub_le_self _ ha.le)
    _ = _ := by
      rw [Real.rpow_def_of_pos (div_pos (mul_pos (Real.exp_pos _) ha) htpos),
        Real.log_div (mul_pos (Real.exp_pos _) ha).ne' htpos.ne',
        Real.log_mul (Real.exp_pos _).ne' ha.ne', Real.log_exp, mul_comm]

end Oberwolfach
