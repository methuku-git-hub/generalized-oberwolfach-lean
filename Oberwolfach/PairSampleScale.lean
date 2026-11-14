module

public import Oberwolfach.SubsetInclusion
public import Mathlib.Data.Nat.Choose.Cast

@[expose] public section

/-! The exact two-vertex inclusion probability and the coefficient scale
obtained by dividing an r-vertex inclusion estimate by it. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def pairSampleProbability (n m : ℕ) : ℝ := (m.choose 2:ℝ)/(n.choose 2:ℝ)

theorem pairSampleProbability_pos {n m : ℕ} (hm : 2≤m) (hmn : m≤n) :
    0<pairSampleProbability n m := by
  apply div_pos
  · exact_mod_cast Nat.choose_pos hm
  · exact_mod_cast Nat.choose_pos (hm.trans hmn)

theorem pairSampleProbability_formula {n m : ℕ} (hm : 2≤m) (hmn : m≤n) :
    pairSampleProbability n m=(m:ℝ)*(m-1)/((n:ℝ)*(n-1)) := by
  unfold pairSampleProbability
  rw [Nat.cast_choose_two,Nat.cast_choose_two]
  field_simp


theorem pairSampleProbability_lower {n m : ℕ} (hm : 2≤m) (hmn : m≤n) :
    ((m:ℝ)/n)^2/2≤pairSampleProbability n m := by
  rw [pairSampleProbability_formula hm hmn]
  have hn : (0:ℝ)<n := Nat.cast_pos.mpr (by omega)
  have hn1 : (0:ℝ)<(n:ℝ)-1 := by
    have hh : (2:ℝ)≤n := by exact_mod_cast hm.trans hmn
    linarith
  have hm2 : (2:ℝ)≤m := by exact_mod_cast hm
  have hd : 0<(n:ℝ)*(n-1) := mul_pos hn hn1
  apply (le_div_iff₀ hd).mpr
  field_simp
  nlinarith [sq_nonneg (m:ℝ),mul_nonneg (show 0≤(m:ℝ)*(m-2) by positivity) hn.le]

theorem fixedSubset_pair_probability {V : Type*} [Fintype V] [DecidableEq V]
    {m : ℕ} [Nonempty (FixedSubset V m)] (hm : m≤Fintype.card V)
    (u v : V) (huv : u≠v) :
    (FiniteLaw.uniform (FixedSubset V m)).probability (fun S => u∈S.val ∧ v∈S.val)=
      pairSampleProbability (Fintype.card V) m := by
  have hh := fixedSubset_joint_inclusion hm ({u,v}:Finset V)
  simpa [huv,pairSampleProbability,Finset.insert_subset_iff,Finset.singleton_subset_iff] using hh

theorem cycle_sample_coefficient_scale {n m r : ℕ} (hm : 2≤m) (hmn : m≤n)
    (hr : 2≤r) (κ : ℝ) (hκ : 0≤κ) (hκ1 : κ≤1) :
    ((m:ℝ)/n)^r/(pairSampleProbability n m/(1+κ))≤
      (4*(m:ℝ)^(r-2))/(n:ℝ)^(r-2) := by
  have hn : (0:ℝ)<n := Nat.cast_pos.mpr (by omega)
  have hm' : (0:ℝ)<m := Nat.cast_pos.mpr (by omega)
  have hx : 0<(m:ℝ)/n := div_pos hm' hn
  have hκ' : 0<1+κ := by linarith
  have hs : 0<((m:ℝ)/n)^2/2 := by positivity
  have hpow : ((m:ℝ)/n)^r=((m:ℝ)/n)^(r-2)*((m:ℝ)/n)^2 := by
    rw [← pow_add,Nat.sub_add_cancel hr]
  calc
    _ = (1+κ)*(((m:ℝ)/n)^r/pairSampleProbability n m) := by
      simp only [div_div_eq_mul_div]
      ring
    _ ≤ (1+κ)*(((m:ℝ)/n)^r/(((m:ℝ)/n)^2/2)) := by
      apply mul_le_mul_of_nonneg_left _ hκ'.le
      exact div_le_div_of_nonneg_left (by positivity) hs (pairSampleProbability_lower hm hmn)
    _ = 2*(1+κ)*((m:ℝ)/n)^(r-2) := by
      rw [hpow]
      field_simp
    _ ≤ 4*((m:ℝ)/n)^(r-2) := by
      have hp : 0≤((m:ℝ)/n)^(r-2) := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hκ1 hp]
    _ = _ := by rw [div_pow];ring

end Oberwolfach
