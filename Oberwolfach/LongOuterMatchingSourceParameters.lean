module

public import Oberwolfach.LongCompatibleLargeSpacingChoices
public import Oberwolfach.LongCapacityAutomaticMargins

@[expose] public section
/-! Choose the common spacing and cutoff for matching and source embedding,
then an order threshold, from the original positive error parameter. -/
set_option autoImplicit false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach

theorem long_outer_matching_source_parameters
    (m dMin:ℕ) (θ:ℝ) (hθ:0<θ):
    ∃d K N:ℕ, 3≤d ∧ dMin≤d ∧ 3≤K ∧
      (1/((m:ℝ)+1))/(d:ℝ)≤θ ∧ 1/(8*(d:ℝ))≤θ/2 ∧
      5/(((m:ℝ)+1)*(d:ℝ)+5)+((m:ℝ)+1)*(d:ℝ)/(K+1)≤θ/2 ∧
      ∀n≥N,8*((m:ℝ)+1)/θ<(n:ℝ)^((1:ℝ)/4) := by
  obtain ⟨d,hd,hdmin,hinv,hcut,hbuffer,hchoices⟩:=
    long_compatible_large_spacing_choices m dMin θ θ hθ hθ
  obtain ⟨K,hK⟩:=exists_nat_gt (max (4*((m:ℝ)+1)*(d:ℝ)/θ) (3:ℝ))
  have hK3:3≤K:=by
    have h:(3:ℝ)<K:=lt_of_le_of_lt (le_max_right _ _) hK
    exact_mod_cast h.le
  have hKlarge:4*((m:ℝ)+1)*(d:ℝ)/θ≤K:=
    (lt_of_le_of_lt (le_max_left _ _) hK).le
  obtain ⟨eps,γ,heps,heps1,hassign,hγ,hγeps,hγhalf,hγd,hγθ,hbound⟩:=hchoices K hK3
  have hsource:=long_capacity_cutoff_succ m d K (by omega) θ (hbound hKlarge)
  have hdR:0<(d:ℝ):=by exact_mod_cast (show 0<d by omega)
  have hspace:1/(8*(d:ℝ))≤θ/2:=by
    have hh:1≤(θ/1024)*(d:ℝ):=(div_le_iff₀ hdR).1 hinv
    apply (div_le_iff₀ (by positivity : 0<8*(d:ℝ))).2
    nlinarith
  obtain ⟨N,hN⟩:=long_capacity_large_order m θ hθ
  exact ⟨d,K,N,hd,hdmin,hK3,hcut,hspace,hsource,hN⟩
end Oberwolfach
