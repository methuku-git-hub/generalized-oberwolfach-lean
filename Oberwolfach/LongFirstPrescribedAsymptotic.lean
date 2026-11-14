module

public import Oberwolfach.LongPrescribedMatchingHubAsymptotic

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_first_prescribed_matching_asymptotic (b ρ:ℝ) (hb:0<b) (hρ:0<ρ):
    ∃N:ℕ,∀n≥N,4*(n:ℝ)^(3/4:ℝ)≤b*n/2 ∧ (n:ℝ)^(3/4:ℝ)≤ρ*n/80000:=by
  obtain ⟨N₁,hN₁⟩:=long_prescribed_matching_hub_asymptotic b hb
  obtain ⟨N₂,hN₂⟩:=eventually_three_quarters_and_constant_le_linear (ρ/80000) 0 (by positivity)
  refine ⟨max N₁ N₂,?_⟩
  intro n hn
  have h₁:=hN₁ n (le_trans (le_max_left _ _) hn)
  have h₂:=hN₂ n (le_trans (le_max_right _ _) hn)
  constructor
  · exact h₁
  · nlinarith only [h₂]
end Oberwolfach
