module

public import Oberwolfach.CapacityPositionDemands
public import Oberwolfach.CapacityPositionWeights

@[expose] public section

/-! The corrections to equal capacity shares have zero total and the stated
pointwise error. Edge-occurrence sums supply the actual linear degree maps. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

def occurrenceSumLinear {V E : Type*} [Fintype E] [DecidableEq V]
    (f : E → V) : (E → ℝ) →ₗ[ℝ] (V → ℝ) where
  toFun w v := ∑ e,if f e=v then w e else 0
  map_add' w u := by
    funext v
    simp only [Pi.add_apply,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    split_ifs <;> ring
  map_smul' s w := by
    funext v
    simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    split_ifs <;> ring

theorem equal_share_correction_total {V : Type*} [Fintype V]
    (k : ℕ) (d O : V → ℝ) (M : ℝ)
    (hd : ∑ v,d v=M) (hO : ∑ v,O v=(k+1)*M) :
    (∑ v,(d v-O v/(k+1:ℝ)))=0 := by
  rw [Finset.sum_sub_distrib,← Finset.sum_div,hd,hO]
  field_simp
  <;> ring

theorem equal_share_correction_bound (k : ℕ) (d O q E : ℝ)
    (hE : 0≤E) (hd : |d-q|≤2*E) (hO : |O-(k+1)*q|≤E) :
    |d-O/(k+1:ℝ)|≤3*E := by
  have hkp : (0:ℝ)<k+1 := by positivity
  have hbase : |O/(k+1:ℝ)-q|≤E := by
    rw [show O/(k+1:ℝ)-q=(O-(k+1)*q)/(k+1:ℝ) by field_simp <;> ring,
      abs_div,abs_of_pos hkp]
    apply (div_le_iff₀ hkp).mpr
    have hk0 : (0:ℝ)≤k := Nat.cast_nonneg k
    nlinarith
  rw [show d-O/(k+1:ℝ)=(d-q)-(O/(k+1:ℝ)-q) by ring]
  have hh := (abs_sub _ _).trans (add_le_add hd hbase)
  linarith

theorem capacityPositionWeights_occurrence_marginals {V E : Type*} [Fintype E] [DecidableEq V]
    (f : E → V) (k : ℕ) (w : E → ℝ) (u : Fin k → E → ℝ)
    (d : Fin (k+1) → V → ℝ)
    (hd : ∀ v,∑ j,d j v=∑ e,if f e=v then w e else 0)
    (hu : ∀ j v,(∑ e,if f e=v then u j e else 0)=
      d j.castSucc v-(∑ e,if f e=v then w e else 0)/(k+1:ℝ)) :
    ∀ j v,(∑ e,if f e=v then capacityPositionWeights k w u j e else 0)=d j v := by
  have hd' : (∑ j,d j)=occurrenceSumLinear f w := by
    funext v
    rw [Finset.sum_apply]
    exact hd v
  have hu' (j : Fin k) : occurrenceSumLinear f (u j)=
      d j.castSucc-(1/(k+1:ℝ)) • occurrenceSumLinear f w := by
    funext v
    change (∑ e,if f e=v then u j e else 0)=
      d j.castSucc v-(1/(k+1:ℝ))*(∑ e,if f e=v then w e else 0)
    rw [hu]
    ring
  have hh := capacityPositionWeights_linear (occurrenceSumLinear f) k w u d hd' hu'
  intro j v
  exact congrFun (hh j) v

end Oberwolfach
