module

public import Oberwolfach.OrdinaryDeepFifteenQuarticPreHostScaleAndSelectedBalanceDecay
public import Oberwolfach.OrdinaryTraceCapacityScaleConstraint

@[expose] public section
/-! The explicit fourteenth-order cover and current recent-window budget
cannot satisfy the required quadratic sampling rate uniformly as the vortex
scale tends to zero. This diagnoses these particular sufficient bounds. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_deep_fifteen_quartic_trace_incompatibility
    (a δcut ρ₀ cLoad:ℝ) (ha:0<a) (hδ:0<δcut) (hρ:0<ρ₀) (hLoad:0<cLoad):
    ∃εcap:ℝ,0<εcap ∧ εcap≤1 ∧ ∀ε aLoad ξroot ηcover ηbal δ rate:ℝ,
      0<ε→ε≤εcap→aLoad=cLoad*ε^14→
      ξroot=min (ε/200) (aLoad^2/160)→ηcover=δcut*(ρ₀/8)*ξroot/1000→
      ηbal≤ηcover→0≤δ→δ≤ηbal→ rate≤δ*(ε/2)^15→¬(4*(a*ε^2)≤rate) :=by
  let C:ℝ:=δcut*(ρ₀/8)*cLoad^2/(160*1000)
  have hC:0<C:=by dsimp [C];positivity
  obtain ⟨εcap,hcap,hcap1,hno⟩:=ordinary_quadratic_sampling_exceeds_twenty_eighth_trace_budget a C ha hC
  refine ⟨εcap,hcap,hcap1,?_⟩
  intro ε aLoad ξroot ηcover ηbal δ rate hε he haLoad hξ hη hbal hδ0 hδη hrate hreq
  have he1:ε≤1:=he.trans hcap1
  have hξbound:ξroot≤aLoad^2/160:=by rw [hξ];exact min_le_right _ _
  have hcover:ηcover≤C*ε^28:=by
    have hh:=mul_le_mul_of_nonneg_left hξbound (show 0≤δcut*(ρ₀/8)/1000 by positivity)
    rw [hη]
    rw [haLoad] at hh
    dsimp [C]
    nlinarith only [hh]
  have hδbound:δ≤C*ε^28:=hδη.trans (hbal.trans hcover)
  have hpow:(ε/2)^15≤1:=pow_le_one₀ (by positivity) (by linarith)
  have hrateδ:rate≤δ:=by
    have hh:=mul_le_mul_of_nonneg_left hpow hδ0
    nlinarith only [hrate,hh]
  exact hno ε δ rate hε he hδbound hrateδ hreq
end Oberwolfach
