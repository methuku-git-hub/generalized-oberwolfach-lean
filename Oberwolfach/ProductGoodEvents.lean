module

public import Oberwolfach.ProductFailureBounds

@[expose] public section

/-! Combine a good first exposure and one simultaneous good event for
all tests in the independent second exposure. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_product_good_lower {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (μ : FiniteLaw Ω) (ν : FiniteLaw Γ) (Good : Ω → Prop) (A : Ω → Γ → Prop)
    (b c : ℝ) (hc : 0≤c) (hgood : 1-b≤μ.probability Good)
    (hsecond : ∀ ω,Good ω → 1-c≤ν.probability (A ω)) :
    1-b-c≤(μ.prod ν).probability (fun z=>Good z.1 ∧ A z.1 z.2) := by
  have hbad : ∀ ω,Good ω → ν.probability (fun γ=>¬A ω γ)≤c := by
    intro ω hω
    have hh := finiteLaw_probability_compl ν (A ω)
    linarith only [hh,hsecond ω hω]
  have hh := finiteLaw_product_rooted_failure μ ν (fun _=>True) (fun ω=>¬Good ω)
    (fun ω γ=>¬(Good ω ∧ A ω γ)) b c hc
    (by
      have hh := finiteLaw_probability_compl μ Good
      have htrue : μ.probability (fun _=>True)=1 := by simp [FiniteLaw.probability,μ.total]
      simpa only [true_and,htrue,mul_one] using (show μ.probability (fun ω=>¬Good ω)≤b by linarith only [hh,hgood]))
    (by
      intro ω hω
      have hg : Good ω := not_not.mp hω
      simpa only [hg,true_and] using hbad ω hg)
  simp only [true_and] at hh
  have htrue : μ.probability (fun _=>True)=1 := by simp [FiniteLaw.probability,μ.total]
  rw [htrue,mul_one] at hh
  have he := finiteLaw_probability_compl (μ.prod ν) (fun z=>Good z.1 ∧ A z.1 z.2)
  linarith only [hh,he]

end Oberwolfach
