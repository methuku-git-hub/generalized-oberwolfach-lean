module

public import Oberwolfach.OrdinaryParentReferenceCompatibleChoiceBeforeSpacing

@[expose] public section
/-! The reference and parent choices are available at every spacing selected
later from the original frequency, density and feasible host margins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach

theorem ordinary_original_parent_reference_before_spacing
    (rstar loadK:ℕ) (hr:4≤rstar) (βfreq ρ₀ α ηP:ℝ)
    (hβ:0<βfreq) (hβ1:βfreq≤1) (hρ:0<ρ₀) (hρ1:ρ₀≤1) (hα:0<α) (hη:0<ηP)
    (hmargin:α/2≤1/2 ∧ max (1/2) (cycleThreshold rstar)+(α/2)/2≤1):
    let pstar:=ρ₀*(βfreq/200)/2
    OrdinaryParentReferenceCompatibleBeforeSpacing (rstar-1) loadK (by omega) (α/2) ρ₀ pstar ηP (by positivity) :=by
  intro pstar
  have hp:0<pstar:=by dsimp [pstar];positivity
  have hs:0<βfreq/200:=by positivity
  have hs1:βfreq/200≤1:=by linarith
  have hp1:pstar≤1:=by
    have hh:=mul_le_mul_of_nonneg_right hρ1 hs.le
    have hm:ρ₀*(βfreq/200)≤1:=by nlinarith [hh,hs1]
    dsimp [pstar]
    nlinarith
  have heq:(rstar-1)+1=rstar:=by omega
  have hmarg:max (1/2) (cycleThreshold ((rstar-1)+1))+(α/2)/2≤1:=by simpa [heq] using hmargin.2
  exact ordinary_parent_reference_compatible_choice_before_spacing (rstar-1) loadK (by omega)
    (α/2) ρ₀ pstar ηP (by positivity) hmargin.1 hmarg hρ hp hp1 hη
end Oberwolfach
