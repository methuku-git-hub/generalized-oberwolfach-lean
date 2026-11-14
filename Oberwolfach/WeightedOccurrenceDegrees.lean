module

public import Oberwolfach.CapacityPositionCorrections
public import Oberwolfach.SignedDemandNormalization

@[expose] public section

/-! Near-unit weights change a degree by at most the weight error times the
actual number of incident edge occurrences. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem weighted_occurrence_degree_error {V E : Type*} [Fintype E] [DecidableEq V]
    (f : E → V) (w : E → ℝ) (κ : ℝ) (hκ : 0≤κ) (hw : ∀ e,|w e-1|≤κ) (v : V) :
    |occurrenceSumLinear f w v-occurrenceDegree f v|≤κ*occurrenceDegree f v := by
  have hd : (∑ e,if f e=v then (1:ℝ) else 0)=occurrenceDegree f v := by
    unfold occurrenceDegree
    apply Finset.sum_congr rfl
    intro e _
    split_ifs <;> rfl
  rw [← hd]
  change |(∑ e,if f e=v then w e else 0)-(∑ e,if f e=v then (1:ℝ) else 0)|≤_
  rw [← Finset.sum_sub_distrib,Finset.mul_sum]
  calc
    _ ≤ ∑ e,|(if f e=v then w e else 0)-(if f e=v then (1:ℝ) else 0)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro e _
      by_cases h : f e=v
      · simpa only [h,ite_true,mul_one] using hw e
      · simp only [h,ite_false,sub_self,abs_zero,mul_zero,le_refl]

theorem weighted_occurrence_degree_near {V E : Type*} [Fintype E] [DecidableEq V]
    (f : E → V) (w : E → ℝ) (κ ε n D : ℝ) (hκ : 0≤κ)
    (hw : ∀ e,|w e-1|≤κ) (v : V)
    (hdeg : occurrenceDegree f v≤n) (hnear : |occurrenceDegree f v-D|≤ε*n) :
    |occurrenceSumLinear f w v-D|≤(ε+κ)*n := by
  have hweight := (weighted_occurrence_degree_error f w κ hκ hw v).trans
    (mul_le_mul_of_nonneg_left hdeg hκ)
  rw [show occurrenceSumLinear f w v-D=
    (occurrenceSumLinear f w v-occurrenceDegree f v)+(occurrenceDegree f v-D) by ring]
  have hh := (abs_add_le _ _).trans (add_le_add hweight hnear)
  nlinarith

theorem occurrence_degree_mean_near {V E : Type*} [Fintype V] [Fintype E]
    (f : E → V) (D ε : ℝ) (hn : 0<Fintype.card V)
    (hnear : ∀ v,|occurrenceDegree f v-D|≤ε) :
    |(Fintype.card E : ℝ)/Fintype.card V-D|≤ε := by
  have hnr : (0:ℝ)<Fintype.card V := Nat.cast_pos.mpr hn
  have he : (Fintype.card E : ℝ)/Fintype.card V-D=
      (∑ v,(occurrenceDegree f v-D))/Fintype.card V := by
    rw [Finset.sum_sub_distrib,occurrenceDegree_total]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    field_simp
  rw [he,abs_div,abs_of_pos hnr]
  apply (div_le_iff₀ hnr).mpr
  have hh := (Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := fun v => occurrenceDegree f v-D)).trans
    (Finset.sum_le_sum (fun v _ => hnear v))
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_comm] using hh

theorem occurrence_degree_near_mean {V E : Type*} [Fintype V] [Fintype E]
    (f : E → V) (D ε : ℝ) (hn : 0<Fintype.card V)
    (hnear : ∀ v,|occurrenceDegree f v-D|≤ε) (v : V) :
    |occurrenceDegree f v-(Fintype.card E : ℝ)/Fintype.card V|≤2*ε := by
  have hm := occurrence_degree_mean_near f D ε hn hnear
  rw [show occurrenceDegree f v-(Fintype.card E : ℝ)/Fintype.card V=
    (occurrenceDegree f v-D)-((Fintype.card E : ℝ)/Fintype.card V-D) by ring]
  have hh := (abs_sub _ _).trans (add_le_add (hnear v) hm)
  linarith

end Oberwolfach
