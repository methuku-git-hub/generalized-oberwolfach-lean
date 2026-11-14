module

public import Oberwolfach.FirstVortexActualSelectorBudgetBundle

@[expose] public section
/-! A loss witness remains valid when the permitted local cap is enlarged. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_summed_loss_local_cap_mono
    (n d:ℕ) (I c c' rho eta θ a γ ξPart κ Δ ζret ηBalance boundary:ℝ)
    (hI:0≤I) (hc:c≤c')
    (h:FirstVortexSummedLossWitness n d I c rho eta θ a γ ξPart κ Δ ζret ηBalance boundary):
    FirstVortexSummedLossWitness n d I c' rho eta θ a γ ξPart κ Δ ζret ηBalance boundary:=by
  obtain ⟨lossInside,inside,loc,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11⟩:=h
  have hm:=mul_le_mul_of_nonneg_right hc hI
  exact ⟨lossInside,inside,loc,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10.trans hm,h11.trans hm⟩
end Oberwolfach
