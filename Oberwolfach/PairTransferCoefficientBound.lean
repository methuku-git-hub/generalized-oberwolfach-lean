module

public import Oberwolfach.OrdinaryVertexTransfer

@[expose] public section

/-! Only ordered pairs containing a wheel's fixed hub can contribute to
its coefficient. Counting these pairs cancels the row-degree normalization. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem pair_fixed_label_count {I U : Type*} [Fintype I]
    (g : I ↪ U) (h : U) :
    (∑ p : I×I,if h=g p.1 ∨ h=g p.2 then (1:ℝ) else 0)≤2*Fintype.card I := by
  have he : (∑ i,if h=g i then (1:ℝ) else 0)=if h∈Set.range g then 1 else 0 := by
    have hh := injective_range_indicator g h
    simpa only [eq_comm] using hh
  calc
    _ ≤ ∑ p : I×I,((if h=g p.1 then (1:ℝ) else 0)+(if h=g p.2 then 1 else 0)) := by
      apply Finset.sum_le_sum
      intro p _
      split_ifs <;> simp_all
    _ = 2*(Fintype.card I:ℝ)*(if h∈Set.range g then 1 else 0) := by
      simp only [Fintype.sum_prod_type,Finset.sum_add_distrib]
      have hfirst : (∑ i : I,∑ j : I,if h=g i then (1:ℝ) else 0) =
          (Fintype.card I:ℝ)*(∑ i : I,if h=g i then (1:ℝ) else 0) := by
        simp_rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
        rw [Finset.mul_sum]
      have hsecond : (∑ i : I,∑ j : I,if h=g j then (1:ℝ) else 0) =
          (Fintype.card I:ℝ)*(∑ j : I,if h=g j then (1:ℝ) else 0) := by
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      rw [hfirst,hsecond,he]
      ring
    _ ≤ _ := by
      split_ifs
      · simp
      · simp only [mul_zero]
        positivity

theorem normalized_pair_transfer_bound {I U : Type*} [Fintype I]
    (g : I ↪ U) (h : U) (a : I → ℝ) (b : I → I → ℝ)
    (η B : ℝ) (hη : 0≤η) (hB : 0≤B)
    (ha : ∀ i,|a i|≤η) (hb : ∀ i j,|b i j|≤B)
    (hz : ∀ i j,h≠g i → h≠g j → b i j=0) :
    |(∑ p : I×I,a p.1*b p.1 p.2)/(Fintype.card I:ℝ)|≤2*η*B := by
  by_cases hI : Fintype.card I=0
  · simp only [hI,Nat.cast_zero,div_zero,abs_zero]
    positivity
  · have hn : (0:ℝ)<Fintype.card I := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hI)
    have hterm (p : I×I) : |a p.1*b p.1 p.2|≤
        η*B*(if h=g p.1 ∨ h=g p.2 then (1:ℝ) else 0) := by
      by_cases hp : h=g p.1 ∨ h=g p.2
      · rw [if_pos hp,mul_one,abs_mul]
        exact mul_le_mul (ha _) (hb _ _) (abs_nonneg _) hη
      · have hi : h≠g p.1 := fun hi => hp (Or.inl hi)
        have hj : h≠g p.2 := fun hj => hp (Or.inr hj)
        rw [hz _ _ hi hj,if_neg hp,mul_zero,mul_zero,abs_zero]
    rw [abs_div,abs_of_nonneg hn.le]
    apply (div_le_iff₀ hn).mpr
    calc
      _ ≤ ∑ p : I×I,|a p.1*b p.1 p.2| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p : I×I,η*B*(if h=g p.1 ∨ h=g p.2 then (1:ℝ) else 0) :=
        Finset.sum_le_sum (fun p _ => hterm p)
      _ = η*B*∑ p : I×I,if h=g p.1 ∨ h=g p.2 then (1:ℝ) else 0 := by rw [Finset.mul_sum]
      _ ≤ η*B*(2*Fintype.card I) := mul_le_mul_of_nonneg_left (pair_fixed_label_count g h) (mul_nonneg hη hB)
      _ = _ := by ring

end Oberwolfach
