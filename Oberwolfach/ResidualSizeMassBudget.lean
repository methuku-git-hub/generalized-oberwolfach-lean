module

public import Oberwolfach.ResidualActualFullSelection

@[expose] public section
/-! Turn an actual full-selection mass bound and an uncovered-spoke bound
into a residual vertex bound without changing the original parameters. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem residual_size_from_mass_and_missing
    (n c d starts cycles full remaining missing:ℕ) (ε κ:ℝ)
    (hbase:full+cycles+(c*d-1)*starts=n)
    (hremaining:remaining≤full+(c+1)*missing)
    (hmass:(1-ε)*n≤(cycles:ℝ)+(c*d-1:ℕ)*starts)
    (hmissing:(missing:ℝ)≤κ*n):
    (remaining:ℝ)≤(ε+(c+1)*κ)*n:=by
  have hb:(full:ℝ)+cycles+(c*d-1:ℕ)*starts=n:=by exact_mod_cast hbase
  have hr:(remaining:ℝ)≤full+(c+1:ℕ)*missing:=by exact_mod_cast hremaining
  have hc:(0:ℝ)≤(c+1:ℕ):=by positivity
  have hh:=mul_le_mul_of_nonneg_left hmissing hc
  push_cast at *
  nlinarith
end Oberwolfach
