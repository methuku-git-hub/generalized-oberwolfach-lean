module

public import Oberwolfach.FirstVortexActualSelectorBudgetBundle

@[expose] public section
/-! The summed-loss bounds with the three witnesses named, for carrying the
same quantitative choices into the later correction and level chain. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

def FirstVortexSummedLossAt
    (n d:ℕ) (I c rho eta θ a γ ξPart κ Δ ζret ηBalance boundary lossInside inside loc:ℝ):Prop :=
    0≤lossInside ∧ 0≤ inside ∧ 0≤loc ∧ loc≤eta*n ∧ inside≤I*eta*n ∧
    0≤2*(boundary+2*(max a γ*n)+((6*d+2:ℕ):ℝ)+(κ*n+1)) ∧
    I*(Δ*n+2*((6*d+2:ℕ):ℝ))+(n:ℝ)*
      (2*(boundary+2*(max a γ*n)+((6*d+2:ℕ):ℝ)+(κ*n+1)))≤lossInside ∧
    I*((n:ℝ)^(3/5:ℝ)+(d:ℝ)*(n:ℝ)^(3/5:ℝ))+lossInside≤ inside ∧
    (n:ℝ)^(3/5:ℝ)+(d:ℝ)*(n:ℝ)^(3/5:ℝ)+
      (Δ*n+2*(boundary+2*(max a γ*n)+((6*d+2:ℕ):ℝ)+(κ*n+1))+(6*d+2:ℕ))≤loc ∧
    ((2*θ+2*max a (4*γ)+2*ξPart)*n+2*(boundary+2*(max a γ*n)+((6*d+2:ℕ):ℝ)+(κ*n+1))+
      (n:ℝ)^(3/5:ℝ)+2*Δ*n+2*(6*d+2:ℕ)+loc+(inside/n+loc)/rho+1)≤c*I ∧
    2*(ζret*n+(boundary+2*(max a γ*n)+((6*d+2:ℕ):ℝ)+(κ*n+1)))+
      (ηBalance*n+2*((2*θ+2*max a (4*γ)+2*ξPart)*n+2*(boundary+2*(max a γ*n)+((6*d+2:ℕ):ℝ)+(κ*n+1))+
        (n:ℝ)^(3/5:ℝ)+2*Δ*n+2*(6*d+2:ℕ)+loc+(inside/n+loc)/rho+1))≤c*I

theorem first_vortex_summed_loss_at_iff
    (n d:ℕ) (I c rho eta θ a γ ξPart κ Δ ζret ηBalance boundary:ℝ):
    FirstVortexSummedLossWitness n d I c rho eta θ a γ ξPart κ Δ ζret ηBalance boundary ↔
      ∃lossInside inside loc:ℝ,FirstVortexSummedLossAt n d I c rho eta θ a γ ξPart κ Δ ζret ηBalance boundary lossInside inside loc :=by
  rfl
end Oberwolfach
