module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Tactic

@[expose] public section

/-! Splitting a capacity into positions, with the final position determined by
subtraction. Linear degree identities and coefficient bounds are preserved. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

def capacityPositionWeights {E : Type*} (k : ℕ) (w : E → ℝ) (u : Fin k → E → ℝ) :
    Fin (k+1) → E → ℝ :=
  Fin.snoc (fun j => (1/(k+1:ℝ)) • w+u j)
    (w-∑ j,((1/(k+1:ℝ)) • w+u j))

theorem capacityPositionWeights_total {E : Type*} (k : ℕ) (w : E → ℝ) (u : Fin k → E → ℝ) :
    (∑ j,capacityPositionWeights k w u j)=w := by
  rw [Fin.sum_univ_castSucc]
  simp only [capacityPositionWeights,Fin.snoc_castSucc,Fin.snoc_last]
  abel

theorem capacityPositionWeights_linear {E W : Type*} [AddCommGroup W] [Module ℝ W]
    (T : (E → ℝ) →ₗ[ℝ] W) (k : ℕ) (w : E → ℝ) (u : Fin k → E → ℝ)
    (d : Fin (k+1) → W) (hd : ∑ j,d j=T w)
    (hu : ∀ j,T (u j)=d j.castSucc-(1/(k+1:ℝ)) • T w) :
    ∀ j,T (capacityPositionWeights k w u j)=d j := by
  have hfirst (j : Fin k) : T ((1/(k+1:ℝ)) • w+u j)=d j.castSucc := by
    rw [map_add,map_smul,hu]
    abel
  intro j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp only [capacityPositionWeights,Fin.snoc_last,map_sub,map_sum,hfirst]
    rw [Fin.sum_univ_castSucc] at hd
    rw [← hd]
    abel
  · simpa only [capacityPositionWeights,Fin.snoc_castSucc] using hfirst j

theorem capacityPositionWeights_last_formula {E : Type*} (k : ℕ) (w : E → ℝ) (u : Fin k → E → ℝ) (e : E) :
    capacityPositionWeights k w u (Fin.last k) e=w e/(k+1:ℝ)-∑ j,u j e := by
  rw [capacityPositionWeights,Fin.snoc_last]
  rw [Pi.sub_apply,Finset.sum_apply]
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  field_simp
  <;> ring

theorem capacityPositionWeights_bounds {E : Type*} (k : ℕ) (hk : 0<k)
    (w : E → ℝ) (u : Fin k → E → ℝ) (κ U : ℝ)
    (hU : 0≤U) (hw : ∀ e,|w e-1|≤κ) (hu : ∀ j e,|u j e|≤U) :
    ∀ j e,|capacityPositionWeights k w u j e-1/(k+1:ℝ)| ≤ κ/(k+1:ℝ)+k*U := by
  have hkp : (0:ℝ)<k+1 := by positivity
  have hkr : (1:ℝ)≤k := by exact_mod_cast hk
  intro j e
  refine Fin.lastCases ?_ (fun j => ?_) j
  · rw [capacityPositionWeights_last_formula]
    rw [show w e/(k+1:ℝ)-(∑ j,u j e)-1/(k+1:ℝ)=(w e-1)/(k+1:ℝ)-(∑ j,u j e) by ring]
    have hbase : |(w e-1)/(k+1:ℝ)| ≤ κ/(k+1:ℝ) := by
      rw [abs_div,abs_of_pos hkp]
      exact div_le_div_of_nonneg_right (hw e) hkp.le
    have hsum : |∑ j,u j e| ≤ (k:ℝ)*U := by
      calc
        _ ≤ ∑ j,|u j e| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _j : Fin k,U := Finset.sum_le_sum (fun j _ => hu j e)
        _ = _ := by simp
    exact (abs_sub _ _).trans (add_le_add hbase hsum)
  · simp only [capacityPositionWeights,Fin.snoc_castSucc,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    rw [show 1/(k+1:ℝ)*w e+u j e-1/(k+1:ℝ)=(w e-1)/(k+1:ℝ)+u j e by ring]
    have hbase : |(w e-1)/(k+1:ℝ)| ≤ κ/(k+1:ℝ) := by
      rw [abs_div,abs_of_pos hkp]
      exact div_le_div_of_nonneg_right (hw e) hkp.le
    have hh := (abs_add_le _ _).trans (add_le_add hbase (hu j e))
    nlinarith

end Oberwolfach
