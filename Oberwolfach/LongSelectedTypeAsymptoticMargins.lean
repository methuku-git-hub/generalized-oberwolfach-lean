module

public import Oberwolfach.ColourRoundErrorMargins

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

/-- For fixed constants, the sampled degree error and the fixed ineligible and
reserve costs fit the two positive linear gaps for all sufficiently large n. -/
theorem long_selected_type_eventual_margins
    (d e:ℕ) (rho ζ δLoss epsilon eta c:ℝ)
    (hbudget:ζ+δLoss<eta) (hsupply:rho+ζ+δLoss+epsilon<c):
    ∃N:ℕ,∀n:ℕ,N≤n→∀I C:ℕ,
      (I:ℝ)≤epsilon*n→C≤e→
      let err:ℝ:=(n:ℝ)^(3/5:ℝ)
      let L:ℝ:=(ζ+δLoss)*n+(6*d+2:ℕ)
      err+(d:ℝ)*err+L≤eta*n ∧
      rho*n+err+L+I+C≤c*n:=by
  let gap:=min (eta-(ζ+δLoss)) (c-(rho+ζ+δLoss+epsilon))
  have hgap:0<gap:=by dsimp [gap];exact lt_min (by linarith) (by linarith)
  obtain ⟨N,hN⟩:=eventually_sublinear_affine_error (1+d) (6*d+2+e) 1 (2/5) gap
    (by positivity) (by positivity) (by norm_num) (by norm_num) hgap
  refine ⟨N,?_⟩
  intro n hn I C hI hC err L
  have hs:=hN n hn err (by dsimp [err];norm_num)
  have hgap1:gap≤eta-(ζ+δLoss):=min_le_left _ _
  have hgap2:gap≤c-(rho+ζ+δLoss+epsilon):=min_le_right _ _
  have hn0:(0:ℝ)≤n:=Nat.cast_nonneg _
  have hs1:=mul_le_mul_of_nonneg_right hgap1 hn0
  have hs2:=mul_le_mul_of_nonneg_right hgap2 hn0
  have hc:(C:ℝ)≤e:=by exact_mod_cast hC
  have herr:0≤err:=by dsimp [err];positivity
  have hd:0≤(d:ℝ):=Nat.cast_nonneg _
  have hde:0≤(d:ℝ)*err:=mul_nonneg hd herr
  constructor <;> dsimp [L] <;> push_cast at * <;>
    nlinarith only [hs,hs1,hs2,hI,hc,hn0,hde]
end Oberwolfach
