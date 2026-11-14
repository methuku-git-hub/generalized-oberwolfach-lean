module

public import Oberwolfach.LongOrderedJointFailureBudget

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_ordered_parent_error_alignment
    (K:ℕ) (hK:3≤K) (θ lam epsOrd epsParent:ℝ)
    (hθ:0<θ) (hθhi:θ≤1/100) (hlam:0<lam) (hlamθ:lam≤θ) (hOrd:0<epsOrd)
    (hParent:0<epsParent)
    (hbudget:3*epsParent≤min lam epsOrd*(θ/(100*(K:ℝ)^2))):
    0<min lam epsOrd ∧ min lam epsOrd≤θ ∧ epsParent≤epsOrd := by
  have hKreal:(1:ℝ)≤K:=by exact_mod_cast (show 1≤K by omega)
  have hden:1≤100*(K:ℝ)^2:=by nlinarith [sq_nonneg ((K:ℝ)-1)]
  have hcoef:θ/(100*(K:ℝ)^2)≤1:=by
    apply (div_le_one (by positivity)).2
    linarith
  have hprod:min lam epsOrd*(θ/(100*(K:ℝ)^2))≤epsOrd:=by
    calc
      _ ≤ min lam epsOrd*1 := mul_le_mul_of_nonneg_left hcoef (le_of_lt (lt_min hlam hOrd))
      _ ≤ epsOrd := by simpa only [mul_one] using (min_le_right lam epsOrd)
  refine ⟨lt_min hlam hOrd,?_,?_⟩
  · exact (min_le_left lam epsOrd).trans hlamθ
  · linarith
end Oberwolfach
