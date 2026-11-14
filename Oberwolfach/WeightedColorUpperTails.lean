module

public import Oberwolfach.WeightedColorChernoff

@[expose] public section

/-! Upper tails using a supplied upper bound on the mean. The bound remains
valid for zero total weight, which is needed for empty degree and codegree tests. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {E C : Type*} [Fintype E] [Fintype C] [DecidableEq E] [Nonempty C]

theorem weightedColor_upper_chernoff (w : E → ℝ) (b : ℝ) (hb : 0<b)
    (hw : ∀ e,0≤w e ∧ w e≤b) (c : C) (U : ℝ) (hU : 0≤U)
    (hmean : (∑ e,w e)/Fintype.card C≤U)
    (ε : ℝ) (he : 0≤ε) (he1 : ε≤1) :
    (FiniteLaw.pi (fun _ : E=>FiniteLaw.uniform C)).probability
      (fun σ=>(1+ε)*U≤∑ e,if σ e=c then w e else 0)≤
      Real.exp (-ε^2*U/(3*b)) := by
  have hp : 0<1+ε := by linarith
  have hlog : 0≤Real.log (1+ε) := Real.log_nonneg (by linarith)
  refine (weightedColor_exponential_tail w b hb hw c (Real.log (1+ε)) ((1+ε)*U) hlog).trans ?_
  rw [Real.exp_log hp]
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ (U*ε-Real.log (1+ε)*((1+ε)*U))/b := by
      apply div_le_div_of_nonneg_right _ hb.le
      have h := mul_le_mul_of_nonneg_right hmean he
      nlinarith
    _ = -(U/b)*((1+ε)*Real.log (1+ε)-ε) := by ring
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (chernoff_upper_entropy he he1) (div_nonneg hU hb.le)
      convert neg_le_neg h using 1 <;> ring

theorem weightedColor_sparse_upper_tail (w : E → ℝ) (b : ℝ) (hb : 0<b)
    (hw : ∀ e,0≤w e ∧ w e≤b) (c : C) (U t : ℝ)
    (hmean : (∑ e,w e)/Fintype.card C≤U)
    (ht : 2*(Real.exp 1-1)*U≤t) :
    (FiniteLaw.pi (fun _ : E=>FiniteLaw.uniform C)).probability
      (fun σ=>t≤∑ e,if σ e=c then w e else 0)≤Real.exp (-t/(2*b)) := by
  refine (weightedColor_exponential_tail w b hb hw c 1 t zero_le_one).trans ?_
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right hmean
    (sub_nonneg.mpr (Real.one_le_exp_iff.mpr zero_le_one))
  calc
    _ ≤ (-t/2)/b := by
      apply div_le_div_of_nonneg_right _ hb.le
      nlinarith
    _ = _ := by ring

end Oberwolfach
