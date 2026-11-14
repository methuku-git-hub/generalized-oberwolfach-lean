module

public import Oberwolfach.UniformSamples

@[expose] public section

/-! A common exchange bound for independent fixed-size class samples.
The exposure bound is the sum of the prescribed sample sizes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {s : ℕ} {V : Fin s → Type*} [∀ i,Fintype (V i)]

theorem uniform_profile_mgf (m : Fin s → ℕ)
    [∀ i,Nonempty (FixedSubset (V i) (m i))]
    (hm : ∀ i,m i ≤ Fintype.card (V i)) (f : (∀ i,FixedSubset (V i) (m i)) → ℝ)
    (K : ℝ) (hK : 0 ≤ K)
    (hchange : ∀ i (σ τ : ∀ j,FixedSubset (V j) (m j)),
      (∀ j,j≠i → σ j=τ j) → ∀ x y,τ i=fixedSubsetMap (Equiv.swap x y) (σ i) → |f σ-f τ| ≤ K)
    (u : ℝ) :
    let μ := FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset (V i) (m i)))
    μ.expectation (fun σ => Real.exp (u*(f σ-μ.expectation f))) ≤
      Real.exp (u^2*((∑ i,(m i:ℝ))*K^2)/8) := by
  let spec := fun i => UniformSampleSpec.subset (m i) (hm i)
  have hchange' : ∀ i (σ τ : ∀ j,(spec j).State),
      (∀ j,j≠i → σ j=τ j) → ∀ x y,τ i=(spec i).exchange x y (σ i) → |f σ-f τ| ≤ K := by
    intro i σ τ ha x y he
    exact hchange i σ τ ha x y he
  have hh := uniformSamples_mgf spec f (fun _ => K) (fun _ => hK) hchange' u
  have hvar : (∑ i,((spec i).exposures:ℝ)*K^2) ≤ (∑ i,(m i:ℝ))*K^2 := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg K)
    exact_mod_cast (Nat.min_le_left (m i) (Fintype.card (V i)-m i))
  have hh' := hh.trans (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hvar (sq_nonneg u)) (by norm_num)))
  simpa only [spec,UniformSampleSpec.law,UniformSampleSpec.State] using hh'

theorem uniform_profile_absolute_tail (m : Fin s → ℕ)
    [∀ i,Nonempty (FixedSubset (V i) (m i))]
    (hm : ∀ i,m i ≤ Fintype.card (V i)) (f : (∀ i,FixedSubset (V i) (m i)) → ℝ)
    (K : ℝ) (hK : 0 ≤ K)
    (hchange : ∀ i (σ τ : ∀ j,FixedSubset (V j) (m j)),
      (∀ j,j≠i → σ j=τ j) → ∀ x y,τ i=fixedSubsetMap (Equiv.swap x y) (σ i) → |f σ-f τ| ≤ K)
    (t : ℝ) (ht : 0 ≤ t) :
    let μ := FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset (V i) (m i)))
    μ.probability (fun σ => t ≤ |f σ-μ.expectation f|) ≤
      2*Real.exp (-2*t^2/((∑ i,(m i:ℝ))*K^2)) := by
  exact finiteLaw_mgf_absolute_tail _ _ (by positivity) (uniform_profile_mgf m hm f K hK hchange) ht

end Oberwolfach
