module

public import Oberwolfach.FirstVortexDensityChoice

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_prescribed_density_choice
    (ρ₀ α C εAbs εMax:ℝ) (hρ:0<ρ₀) (hα:0<α) (hC:0<C) (hAbs:0<εAbs) (hMax:0<εMax):
    ∃ε:ℝ,0<ε ∧ ε<1/4 ∧ ε≤εAbs ∧ ε≤εMax ∧ ε≤(ρ₀/4)/80000 ∧ ε≤α/(1000*C):=
  first_vortex_density_choice (ρ₀/4) α C εAbs εMax (by positivity) hα hC hAbs hMax
end Oberwolfach
