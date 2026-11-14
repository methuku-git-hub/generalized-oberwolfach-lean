module

public import Oberwolfach.UniformProfileConcentration

@[expose] public section

/-! Concentration with a constant exponential rate in the sample
order. The variance bound is positive even when some classes are empty. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {s : ℕ} {V : Fin s → Type*} [∀ i,Fintype (V i)]

theorem uniform_profile_linear_rate_tail (m : Fin s → ℕ)
    [∀ i,Nonempty (FixedSubset (V i) (m i))]
    (hm : ∀ i,m i ≤ Fintype.card (V i))
    (f : (∀ i,FixedSubset (V i) (m i)) → ℝ) (c L t ξ : ℝ)
    (hc : 0 < c) (hL : 0 < L) (ht : 0 < t) (hξ : 0 ≤ ξ)
    (hsteps : ∑ i,(m i:ℝ) ≤ c*t)
    (hexchange : ∀ i σ τ,(∀ j,j≠i → σ j=τ j) → ∀ x y : V i,
      τ i=fixedSubsetMap (Equiv.swap x y) (σ i) → |f σ-f τ| ≤ L/t) :
    let μ := FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset (V i) (m i)))
    μ.probability (fun σ => ξ ≤ |f σ-μ.expectation f|) ≤
      2*Real.exp (-(2*ξ^2/(c*L^2))*t) := by
  let μ := FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset (V i) (m i)))
  have hvar : (∑ i,(m i:ℝ))*(L/t)^2 ≤ c*L^2/t := by
    calc
      _ ≤ (c*t)*(L/t)^2 := mul_le_mul_of_nonneg_right hsteps (sq_nonneg _)
      _ = _ := by field_simp
  have hmgf (u : ℝ) : μ.expectation (fun σ => Real.exp (u*(f σ-μ.expectation f))) ≤
      Real.exp (u^2*(c*L^2/t)/8) := by
    have hh := uniform_profile_mgf m hm f (L/t) (by positivity) hexchange u
    apply hh.trans
    apply Real.exp_le_exp.mpr
    have hh' := mul_le_mul_of_nonneg_left hvar (sq_nonneg u)
    nlinarith
  have hh := finiteLaw_mgf_absolute_tail μ f (v:=c*L^2/t) (by positivity) hmgf (t:=ξ) hξ
  change _ ≤ _
  have he : -2*ξ^2/(c*L^2/t)=-(2*ξ^2/(c*L^2))*t := by field_simp
  rw [he] at hh
  exact hh

theorem degree_sample_exchange_coefficient (c : ℕ) (hc : 2 ≤ c)
    (J B t n : ℝ) (hJ : 0 ≤ J) (hB : 0 ≤ B) (ht : 0 < t)
    (hn0 : 0 ≤ n) (hn : n ≤ (2*c+1)*t) :
    2*J*n^(c-2)*(B/t^(c-1)) ≤ (2*J*(2*c+1)^(c-2)*B)/t := by
  have hp := pow_le_pow_left₀ hn0 hn (c-2)
  calc
    _ ≤ 2*J*((2*c+1)*t)^(c-2)*(B/t^(c-1)) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by positivity)) (by positivity)
    _ = _ := by
      rw [mul_pow]
      have he : t^(c-1)=t^(c-2)*t := by rw [← pow_succ];congr 1;omega
      rw [he]
      field_simp

end Oberwolfach
