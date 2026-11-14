module

public import Oberwolfach.OrdinaryRawParentReferenceRimJoint
public import Oberwolfach.CoordinateLocalLemma

@[expose] public section
/-! The explicit probability estimate for the common raw parent and cut
    event is positive once both domains contain at least sixteen vertices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_raw_parent_reference_rim_positive_bound
    (n m : ℕ) (hn : 16≤n) (hm : 16≤m) :
    0 < 1-(1/(n:ℝ)+3/(n:ℝ)^2)-3/(m:ℝ)^1-1/(n:ℝ)^1-1/(m:ℝ)^1 := by
  have hn16 : (16:ℝ)≤n := by exact_mod_cast hn
  have hm16 : (16:ℝ)≤m := by exact_mod_cast hm
  have hn0 : (0:ℝ)<n := by linarith
  have hnsq : (1:ℝ)/(n:ℝ)^2≤1/n := by
    apply one_div_le_one_div_of_le hn0
    nlinarith
  have hni : (1:ℝ)/n≤1/16 := one_div_le_one_div_of_le (by norm_num) hn16
  have hmi : (1:ℝ)/m≤1/16 := one_div_le_one_div_of_le (by norm_num) hm16
  have hthree : (3:ℝ)/(n:ℝ)^2≤3*(1/n) := by
    have h := mul_le_mul_of_nonneg_left hnsq (show (0:ℝ)≤3 by norm_num)
    simpa only [div_eq_mul_inv,one_mul] using h
  have hmthree : (3:ℝ)/m=3*(1/m) := by ring
  simp only [pow_one]
  rw [hmthree]
  linarith

theorem ordinary_raw_parent_reference_rim_positive_event
    {Ω : Type} [Fintype Ω] (μ : FiniteLaw Ω) (E : Ω→Prop) (n m : ℕ)
    (hn : 16≤n) (hm : 16≤m)
    (hprob : 1-(1/(n:ℝ)+3/(n:ℝ)^2)-3/(m:ℝ)^1-1/(n:ℝ)^1-1/(m:ℝ)^1≤μ.probability E) :
    ∃ z,0<μ.mass z ∧ E z :=
  finiteLaw_positive_event_exists μ E ((ordinary_raw_parent_reference_rim_positive_bound n m hn hm).trans_le hprob)
end Oberwolfach
