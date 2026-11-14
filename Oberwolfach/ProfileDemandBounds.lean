module

public import Oberwolfach.ProfileDemandCoefficients

@[expose] public section

/-! Uniform bounds for the explicit signed root-demand coefficients.
No change is made to the fixed root law or to the vertex classes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
    {V : I → Type*} [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]

theorem profileDemandMultiplier_bounds (a : I → ℕ) (k : ℝ) (hk : 2 ≤ k)
    (ha : ∀ i,1 ≤ a i) (hn : ∀ i,(Fintype.card (V i):ℝ)=(a i:ℝ)*k) (i : I) :
    0 ≤ profileDemandMultiplier (V:=V) a i ∧ profileDemandMultiplier (V:=V) a i ≤ 2*k := by
  have hai : (1:ℝ) ≤ a i := by exact_mod_cast ha i
  have hni : (2:ℝ) ≤ Fintype.card (V i) := by rw [hn i];nlinarith
  have hdiff : (0:ℝ)<Fintype.card (V i)-a i := by rw [hn i];nlinarith
  constructor
  · dsimp [profileDemandMultiplier]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith))
      (mul_nonneg (Nat.cast_nonneg _) hdiff.le)
  · apply (div_le_iff₀ (mul_pos (by linarith : (0:ℝ)<a i) hdiff)).mpr
    have hcmp : (Fintype.card (V i):ℝ)-1 ≤ 2*(Fintype.card (V i)-a i) := by rw [hn i];nlinarith
    have hh := mul_le_mul_of_nonneg_left hcmp (by positivity : (0:ℝ) ≤ Fintype.card (V i))
    rw [hn i] at hh ⊢
    nlinarith only [hh]

theorem profileDemandCoefficient_bound (a : I → ℕ) (k mean η : ℝ) (hk : 2 ≤ k)
    (hη : 0 ≤ η) (ha : ∀ i,1 ≤ a i)
    (hn : ∀ i,(Fintype.card (V i):ℝ)=(a i:ℝ)*k)
    (hmean : |mean| ≤ η) (y : ∀ i,V i → ℝ) (hy : ∀ i v,|y i v| ≤ 2*η)
    (σ : ∀ i,FixedSubset (V i) (a i)) :
    |profileDemandCoefficient a k mean y σ| ≤ (1+4*(∑ i,(a i:ℝ)))*η*k := by
  have hk0 : 0 ≤ k := by linarith
  have hsum (i : I) : |∑ v∈(σ i).val,y i v| ≤ 2*η*a i := by
    calc
      _ ≤ ∑ v∈(σ i).val,|y i v| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _v∈(σ i).val,2*η := Finset.sum_le_sum (fun v _ => hy i v)
      _ = _ := by simp only [Finset.sum_const,(σ i).property,nsmul_eq_mul];ring
  have hterm (i : I) : |profileDemandMultiplier (V:=V) a i*(∑ v∈(σ i).val,y i v)| ≤ 4*k*η*a i := by
    rw [abs_mul,abs_of_nonneg (profileDemandMultiplier_bounds a k hk ha hn i).1]
    calc
      _ ≤ (2*k)*(2*η*a i) := mul_le_mul (profileDemandMultiplier_bounds a k hk ha hn i).2
        (hsum i) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ |k*mean|+|∑ i,profileDemandMultiplier (V:=V) a i*(∑ v∈(σ i).val,y i v)| := abs_add_le _ _
    _ ≤ k*η+∑ i,|profileDemandMultiplier (V:=V) a i*(∑ v∈(σ i).val,y i v)| := by
      apply add_le_add
      · rw [abs_mul,abs_of_nonneg hk0]
        exact mul_le_mul_of_nonneg_left hmean hk0
      · exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ k*η+∑ i,4*k*η*a i := add_le_add le_rfl (Finset.sum_le_sum (fun i _ => hterm i))
    _ = _ := by rw [← Finset.mul_sum];ring

end Oberwolfach
