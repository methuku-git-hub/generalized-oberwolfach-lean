module

public import Oberwolfach.LongAssignedTotalSamplingMass

@[expose] public section
/-! Convert the sampled long and ordinary mass into the full-selection
vertex mass, retaining every error term explicitly. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem residual_full_mass_from_sampled_counts
    (n c d q kept θ ε₀ errS errC err:ℝ)
    (hn:0≤n) (hd:0<d) (hcd:1≤c*d)
    (S C:ℝ)
    (hS:n*q/d-errS≤S) (hC:n*((1-θ)*kept)-errC≤C)
    (hprob:1-ε₀≤c*q+(1-θ)*kept)
    (herror:n*q/d+(c*d-1)*errS+errC≤err*n):
    (1-ε₀-err)*n≤C+(c*d-1)*S:=by
  have hSmul:=mul_le_mul_of_nonneg_left hS (show 0≤c*d-1 by linarith)
  have hprobmul:=mul_le_mul_of_nonneg_right hprob hn
  have heq:(c*d-1)*(n*q/d)=c*q*n-n*q/d:=by field_simp
  nlinarith
end Oberwolfach
