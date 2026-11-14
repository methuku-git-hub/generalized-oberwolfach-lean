module

public import Oberwolfach.BoundedDifferences
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

@[expose] public section

/-! Hölder interpolation for exponential moments of a finite law, proved
directly from convexity of the exponential function. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem finiteLaw_exponential_interpolation
    {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (X Y : Ω → ℝ)
    {a b θ : ℝ} (hθ0 : 0≤θ) (hθ1 : θ≤1)
    (hX : μ.expectation (fun ω=>Real.exp (X ω))≤Real.exp a)
    (hY : μ.expectation (fun ω=>Real.exp (Y ω))≤Real.exp b) :
    μ.expectation (fun ω=>Real.exp (θ*X ω+(1-θ)*Y ω))≤
      Real.exp (θ*a+(1-θ)*b) := by
  have hpoint (ω : Ω) :
      Real.exp (θ*X ω+(1-θ)*Y ω)≤
        Real.exp (θ*a+(1-θ)*b)*
          (θ*Real.exp (-a)*Real.exp (X ω)+(1-θ)*Real.exp (-b)*Real.exp (Y ω)) := by
    have hc := convexOn_exp.2 (Set.mem_univ (X ω-a)) (Set.mem_univ (Y ω-b))
      hθ0 (sub_nonneg.mpr hθ1) (by ring : θ+(1-θ)=1)
    simp only [smul_eq_mul] at hc
    have hh := mul_le_mul_of_nonneg_left hc (Real.exp_pos (θ*a+(1-θ)*b)).le
    rw [← Real.exp_add] at hh
    have he : θ*a+(1-θ)*b+(θ*(X ω-a)+(1-θ)*(Y ω-b))=
        θ*X ω+(1-θ)*Y ω := by ring
    rw [he] at hh
    simpa only [sub_eq_add_neg,Real.exp_add,Real.exp_neg,mul_assoc,mul_comm,mul_left_comm] using hh
  have he : μ.expectation (fun ω=>Real.exp (θ*a+(1-θ)*b)*
      (θ*Real.exp (-a)*Real.exp (X ω)+(1-θ)*Real.exp (-b)*Real.exp (Y ω)))=
      Real.exp (θ*a+(1-θ)*b)*
        (θ*Real.exp (-a)*μ.expectation (fun ω=>Real.exp (X ω))+
          (1-θ)*Real.exp (-b)*μ.expectation (fun ω=>Real.exp (Y ω))) := by
    simp only [FiniteLaw.expectation,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ω _
    ring
  have hx := mul_le_mul_of_nonneg_left hX (mul_nonneg hθ0 (Real.exp_pos (-a)).le)
  have hy := mul_le_mul_of_nonneg_left hY
    (mul_nonneg (sub_nonneg.mpr hθ1) (Real.exp_pos (-b)).le)
  have hxa : θ*Real.exp (-a)*Real.exp a=θ := by
    rw [mul_assoc,← Real.exp_add];simp
  have hyb : (1-θ)*Real.exp (-b)*Real.exp b=1-θ := by
    rw [mul_assoc,← Real.exp_add];simp
  rw [hxa] at hx
  rw [hyb] at hy
  calc
    _ ≤ _ := finiteLaw_expectation_mono μ _ _ hpoint
    _ = _ := he
    _ ≤ Real.exp (θ*a+(1-θ)*b)*1 :=
      mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
    _ = _ := mul_one _

end Oberwolfach
