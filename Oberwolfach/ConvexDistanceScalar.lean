module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Tactic

@[expose] public section

/-! The scalar estimate in the finite-product convex-distance inequality.
It includes the zero-fibre case; no logarithm of a probability zero is used
to choose the mixing parameter. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Oberwolfach

theorem convexDistance_log_bound {r : ℝ} (hr0 : 1/2≤r) (hr1 : r≤1) :
    -(2*r-1)*Real.log r+(1-r)^2≤Real.log (2-r) := by
  let f : ℝ → ℝ := fun x=>Real.log (2-x)+(2*x-1)*Real.log x-(1-x)^2
  have hd (x : ℝ) (hx : x∈Set.Icc (1/2 : ℝ) 1) :
      HasDerivAt f (-(2-x)⁻¹+2*Real.log x+(2*x-1)*x⁻¹+2*(1-x)) x := by
    have hx0 : x≠0 := by linarith [hx.1]
    have hx2 : 2-x≠0 := by linarith [hx.2]
    convert (((((hasDerivAt_const x 2).sub (hasDerivAt_id x)).log hx2).add
      ((((hasDerivAt_const x 2).mul (hasDerivAt_id x)).sub (hasDerivAt_const x 1)).mul
        ((hasDerivAt_id x).log hx0))).sub
      (((hasDerivAt_const x 1).sub (hasDerivAt_id x)).pow 2)) using 1 <;>
      dsimp [f] <;> try ring
    all_goals
      funext y
      simp only [Pi.add_apply,Pi.mul_apply,Pi.sub_apply,Pi.pow_apply,Pi.ofNat_apply,id_eq]
      ring
  have hm : AntitoneOn f (Set.Icc (1/2 : ℝ) 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    · intro x hx
      exact (hd x hx).continuousAt.continuousWithinAt
    · intro x hx
      exact (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' := interior_subset hx
      rw [(hd x hx').deriv]
      have hx0 : 0<x := by linarith [hx'.1]
      have hx2 : 0<2-x := by linarith [hx'.2]
      have hl := Real.log_le_sub_one_of_pos hx0
      have he : -(2-x)⁻¹+(2*x-1)*x⁻¹ =
          -2*(x-1)^2/(x*(2-x)) := by
        field_simp
        <;> ring
      have hn : -2*(x-1)^2/(x*(2-x))≤0 :=
        div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg (x-1)]) (by positivity)
      rw [← he] at hn
      linarith
  have hh := hm ⟨hr0,hr1⟩ (show (1 : ℝ)∈Set.Icc (1/2) 1 by constructor <;> norm_num) hr1
  dsimp [f] at hh
  norm_num at hh
  linarith

theorem convexDistance_scalar_choice {r : ℝ} (hr0 : 0≤r) (hr1 : r≤1) :
    ∃ θ : ℝ,0≤θ ∧ θ≤1 ∧ (r=0 → θ=0) ∧
      Real.exp ((1-θ)^2/4) * r^(-θ) ≤ 2-r := by
  by_cases hhalf : r≤1/2
  · refine ⟨0,le_refl _,by norm_num,fun _=>rfl,?_⟩
    have he := Real.exp_bound_div_one_sub_of_interval (x:=(1/4 : ℝ))
      (by norm_num) (by norm_num)
    norm_num at he ⊢
    linarith
  · have hr : 0<r := by linarith
    refine ⟨2*r-1,by linarith,by linarith,fun hz=>by linarith,?_⟩
    rw [Real.rpow_def_of_pos hr,← Real.exp_add]
    apply (Real.exp_le_exp.mpr ?_).trans_eq (Real.exp_log (by linarith : 0<2-r))
    have hh := convexDistance_log_bound (le_of_lt (lt_of_not_ge hhalf)) hr1
    nlinarith

end Oberwolfach
