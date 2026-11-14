module

public import Oberwolfach.OrdinaryDeepTraceCoverAndSeparatedBalanceExplicit

@[expose] public section
/-! With a quadratic cover load, the explicit correction tolerance is bounded
below by a fixed multiple of the fourth power of the vortex scale. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_explicit_correction_twenty_eighth_lower
    (δcut ρ₀ cLoad:ℝ) (hδ:0<δcut) (hρ:0<ρ₀) (hLoad:0<cLoad):
    ∃cEta:ℝ,0<cEta ∧ ∀ε:ℝ,0<ε→ε≤1→
      cEta*ε^28≤δcut*(ρ₀/8)*(min (ε/200) ((cLoad*ε^14)^2/160))/1000 :=by
  let cξ:ℝ:=min (1/200) (cLoad^2/160)
  have hcξ:0<cξ:=by dsimp [cξ];positivity
  let cEta:ℝ:=δcut*(ρ₀/8)*cξ/1000
  have hcEta:0<cEta:=by dsimp [cEta];positivity
  refine ⟨cEta,hcEta,?_⟩
  intro ε hε hε1
  have h27:ε^27≤1:=pow_le_one₀ hε.le hε1
  have h4ε:ε^28≤ε:=by
    have hh:=mul_le_mul_of_nonneg_right h27 hε.le
    nlinarith only [hh]
  have hξ:cξ*ε^28≤min (ε/200) ((cLoad*ε^14)^2/160):=by
    apply le_min
    · have hc: cξ≤(1/200:ℝ):=by dsimp [cξ];exact min_le_left _ _
      have hh:=mul_le_mul_of_nonneg_right hc (show 0≤ε^28 by positivity)
      nlinarith only [hh,h4ε]
    · have hc:cξ≤cLoad^2/160:=by dsimp [cξ];exact min_le_right _ _
      have hh:=mul_le_mul_of_nonneg_right hc (show 0≤ε^28 by positivity)
      nlinarith only [hh]
  have hm:=mul_le_mul_of_nonneg_left hξ (show 0≤δcut*(ρ₀/8)/1000 by positivity)
  dsimp [cEta]
  nlinarith only [hm]
end Oberwolfach
