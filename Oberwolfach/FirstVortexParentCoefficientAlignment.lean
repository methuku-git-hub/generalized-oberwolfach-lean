module

public import Mathlib.Tactic

@[expose] public section
/-! The level theorem uses a conservative seed-density denominator.  Its
parent and active error coefficients dominate those of the actual selector. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_weight_coefficient_antitone
    (C B x y:ℝ) (e:ℕ) (hC:0≤C) (hB:0≤B) (hx:0<x) (hxy:x≤y):
    C*(2*B/y^e)≤C*(2*B/x^e) :=by
  have hpow: x^e≤y^e:=pow_le_pow_left₀ hx.le hxy e
  have hdiv:2*B/y^e≤2*B/x^e:=div_le_div_of_nonneg_left (by positivity) (pow_pos hx e) hpow
  exact mul_le_mul_of_nonneg_left hdiv hC

theorem first_vortex_parent_coefficient_alignment
    (r:ℕ) (ρ₀ sstar tstar B δ ε:ℝ)
    (hρ₀:0<ρ₀) (hs:0<sstar) (ht:0<tstar)
    (htsmall:tstar≤sstar/(((r+4):ℕ):ℝ)) (hB:0≤B) (hδ:0≤δ) (hε:0<ε):
    let m:ℝ:=((r+4):ℕ)
    let pLevel:=ρ₀*tstar/2
    let pSelector:=ρ₀*sstar/(2*m)
    let CpLevel:=11*(m+1)^4*(2*B/pLevel^(2*(r+4)+1))
    let CpSelector:=11*(m+1)^4*(2*B/pSelector^(2*(r+4)+1))
    let ClLevel:=5*(m+1)^4*(2*B/pLevel^(2*(r+4)+1))
    let ClSelector:=5*(m+1)^4*(2*B/pSelector^(2*(r+4)+1));
    0<pLevel ∧ pLevel≤pSelector ∧
      CpSelector*δ≤CpLevel*δ ∧ ClSelector*δ≤ClLevel*δ ∧
      ClSelector*(4/ε)*δ≤ClLevel*(4/ε)*δ :=by
  intro m pLevel pSelector CpLevel CpSelector ClLevel ClSelector
  have hm:0<m:=by dsimp [m];positivity
  have hp:0<pLevel:=by dsimp [pLevel];positivity
  have hratio:=mul_le_mul_of_nonneg_left htsmall hρ₀.le
  have hporder:pLevel≤pSelector:=by
    dsimp [pLevel,pSelector]
    have heq:ρ₀*(sstar/m)/2=ρ₀*sstar/(2*m):=by ring
    rw [←heq]
    linarith
  have hCp:CpSelector≤CpLevel:=by
    dsimp [CpSelector,CpLevel]
    exact first_vortex_weight_coefficient_antitone (11*(m+1)^4) B pLevel pSelector (2*(r+4)+1) (by positivity) hB hp hporder
  have hCl:ClSelector≤ClLevel:=by
    dsimp [ClSelector,ClLevel]
    exact first_vortex_weight_coefficient_antitone (5*(m+1)^4) B pLevel pSelector (2*(r+4)+1) (by positivity) hB hp hporder
  have hCpδ:=mul_le_mul_of_nonneg_right hCp hδ
  have hClδ:=mul_le_mul_of_nonneg_right hCl hδ
  have hwide:0≤(4/ε)*δ:=mul_nonneg (by positivity) hδ
  have hClwide:=mul_le_mul_of_nonneg_right hCl hwide
  exact ⟨hp,hporder,hCpδ,hClδ,by nlinarith only [hClwide]⟩
end Oberwolfach
