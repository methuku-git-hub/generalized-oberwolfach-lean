module

public import Mathlib.Tactic
public import Mathlib.Basic.Real.Basic

@[expose] public section

/-! Numerical substitution of the actual physical and auxiliary restoration
bounds. The comparison uses the original order and an explicit lower bound
on the inner order. -/
set_option autoImplicit false
namespace Oberwolfach

theorem marked_protected_final_incidence_budget
    (gamma sigma iota mu nu C₀ n inner ambient:ℝ)
    (hg:0≤ gamma) (hiota:0≤ iota) (hmu:0≤ mu) (hnu:0≤ nu) (hn:0≤ n) (hinner:0≤ inner)
    (hsize:iota*n≤ inner) (hambient:ambient≤ 2*n)
    (hcor:C₀≤ 3*mu*inner) (hmuGamma:mu≤ gamma/12) (hmuSigma:6*mu≤ sigma)
    (hnuGamma:nu≤ gamma*iota/16):
    2*C₀+4*(nu*ambient)≤ gamma*inner∧ 2*C₀≤ sigma*inner:=by
  have h1:=mul_le_mul_of_nonneg_right hmuGamma hinner
  have h2:=mul_le_mul_of_nonneg_left hambient hnu
  have h3:=mul_le_mul_of_nonneg_right hnuGamma hn
  have h4:=mul_le_mul_of_nonneg_left hsize hg
  have h5:=mul_le_mul_of_nonneg_right hmuSigma hinner
  constructor
  · nlinarith only [hcor,h1,h2,h3,h4]
  · nlinarith only [hcor,h5]

theorem marked_protected_final_positive_scales
    (gamma sigma iota muMax:ℝ) (hg:0< gamma) (hs:0< sigma) (hi:0< iota) (hm:0< muMax):
    ∃ nu muCap:ℝ,0< nu∧ 0< muCap∧ nu≤ gamma*iota/16∧ muCap≤ muMax∧ 
      ∀ mu:ℝ,0≤ mu→ mu≤ muCap→ mu≤ gamma/12∧ 6*mu≤ sigma:=by
  refine ⟨gamma*iota/32,min muMax (min (gamma/24) (sigma/12)),by positivity,by positivity,?_,min_le_left _ _,?_⟩
  · have hgi:0≤ gamma*iota:=mul_nonneg hg.le hi.le
    linarith
  · intro mu hmu hcap
    have hγ:=hcap.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hσ:=hcap.trans ((min_le_right _ _).trans (min_le_right _ _))
    constructor <;> linarith

end Oberwolfach
