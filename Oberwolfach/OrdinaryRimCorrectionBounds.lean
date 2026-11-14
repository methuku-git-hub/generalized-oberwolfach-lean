module

public import Oberwolfach.SymmetricEdgeCorrection
public import Oberwolfach.TwoRootCoefficientSum
public import Oberwolfach.PairTransferCoefficientBound

@[expose] public section

/-! Coefficient and spoke-load bounds for the total rim correction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_rim_correction_bounds {V U : Type*} [Fintype V] [Fintype U]
    [DecidableEq V] [DecidableEq U] {r : ℕ} (hr : 3≤r)
    {Q F : SimpleGraph V} {H : V → U → Prop}
    (ψ : OrdinaryWheel Q F H r → ℝ)
    (I : V → V → OrdinaryWheel Q F H r → ℝ)
    (γ η : ℝ) (hγ : 0<γ) (hη : 0≤η) (hn : 0<Fintype.card V)
    (herr : ∀ x y,|ordinaryRimResidual ψ x y|≤η)
    (hdiag : ∀ x D,I x x D=0)
    (hb : ∀ x y,x≠y → ∀ D,|I x y D|≤1/(γ*(Fintype.card V:ℝ)^
      (((ordinaryWheelRim D).support.toFinset∪{x,y}).card-1)))
    (hs : ∀ x y v u,|ordinarySpokeLoad (I x y) v u|≤
      (if v=x ∨ v=y then (1:ℝ) else 0)/(2*γ*Fintype.card V)) :
    (∀ D,|(∑ p : V×V,(ordinaryRimResidual ψ p.1 p.2/2)*I p.1 p.2 D)|≤
      η*(r+1)^2/(γ*(Fintype.card V:ℝ)^(r-1))) ∧
    (∀ v u,|ordinarySpokeLoad (fun D => ∑ p : V×V,
      (ordinaryRimResidual ψ p.1 p.2/2)*I p.1 p.2 D) v u|≤η/γ) := by
  have hn' : (0:ℝ)<Fintype.card V := Nat.cast_pos.mpr hn
  have hz (x y : V) : |ordinaryRimResidual ψ x y/2|≤η := by
    rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    exact (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr (by linarith [herr x y])
  constructor
  · intro D
    have hsum := two_root_coefficient_sum (ordinaryWheelRim D).support.toFinset
      (show 1≤r by omega) D.val.1.val.property.support_card γ hγ hn
      (fun x y => |I x y D|) (fun _ _ => abs_nonneg _)
      (fun x => by rw [hdiag,abs_zero]) (fun x y hxy => hb x y hxy D)
    calc
      _ ≤ ∑ p : V×V,|(ordinaryRimResidual ψ p.1 p.2/2)*I p.1 p.2 D| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p : V×V,η*|I p.1 p.2 D| := by
        apply Finset.sum_le_sum
        intro p _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hz p.1 p.2) (abs_nonneg _)
      _ = η*(∑ x,∑ y,|I x y D|) := by rw [← Finset.mul_sum,Fintype.sum_prod_type]
      _ ≤ η*((r+1)^2/(γ*(Fintype.card V:ℝ)^(r-1))) :=
        mul_le_mul_of_nonneg_left hsum hη
      _ = _ := by ring
  · intro v u
    rw [ordinarySpokeLoad_combination]
    have hcount : (∑ p : V×V,if v=p.1 ∨ v=p.2 then (1:ℝ) else 0)≤2*Fintype.card V := by
      have hh := pair_fixed_label_count (Function.Embedding.refl V) v
      simp only [Function.Embedding.refl_apply] at hh
      exact hh
    calc
      _ ≤ ∑ p : V×V,|(ordinaryRimResidual ψ p.1 p.2/2)*ordinarySpokeLoad (I p.1 p.2) v u| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p : V×V,η*((if v=p.1 ∨ v=p.2 then (1:ℝ) else 0)/(2*γ*Fintype.card V)) := by
        apply Finset.sum_le_sum
        intro p _
        rw [abs_mul]
        exact mul_le_mul (hz p.1 p.2) (hs p.1 p.2 v u) (abs_nonneg _) hη
      _ = η*((∑ p : V×V,if v=p.1 ∨ v=p.2 then (1:ℝ) else 0)/(2*γ*Fintype.card V)) := by
        rw [← Finset.mul_sum,Finset.sum_div]
      _ ≤ η*((2*Fintype.card V)/(2*γ*Fintype.card V)) := by
        exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hcount (by positivity)) hη
      _ = _ := by field_simp

end Oberwolfach
