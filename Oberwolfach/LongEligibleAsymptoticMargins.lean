module

public import Oberwolfach.LongSelectedTypeAsymptoticMargins

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach

theorem long_eligible_type_eventual_margins
    (d e:ℕ) (rho ζ δLoss epsilon eta c:ℝ)
    (hbudget:ζ+δLoss<eta) (hsupply:rho+ζ+δLoss+epsilon<c):
    ∃N:ℕ,∀n:ℕ,N≤n→∀I C:ℕ,
      (I:ℝ)≤epsilon*n→C≤e→
      let err:ℝ:=(n:ℝ)^(3/5:ℝ)
      let L:ℝ:=(ζ+δLoss)*n+(6*d+2:ℕ)
      err+(d:ℝ)*err+L≤eta*n ∧
      rho*n+err+L+I+C+(6*d+2:ℕ)≤c*n:=by
  obtain ⟨N,hN⟩:=long_selected_type_eventual_margins d (e+(6*d+2)) rho ζ δLoss epsilon eta c hbudget hsupply
  refine ⟨N,?_⟩
  intro n hn I C hI hC err L
  have hh:=hN n hn I (C+(6*d+2)) hI (by omega)
  constructor
  · exact hh.1
  · dsimp [err,L]
    push_cast at hh ⊢
    linarith only [hh.2]
end Oberwolfach
