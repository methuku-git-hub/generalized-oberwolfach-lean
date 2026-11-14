module

public import Oberwolfach.MarkedTwoStageCanonicalDensities

@[expose] public section
/-! Choose the inner-set and first-packing scales after both sampled
cover-down theorems have fixed their constants. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
theorem marked_two_stage_choose_inner_and_packing_scales
    (r:ℕ) (beta zeta delta eta₀:ℝ)
    (hb:0<beta) (hz:0<zeta) (hd:0<delta) (he:0<eta₀):
    ∃ xi etaE:ℝ,0<xi ∧ 0<etaE ∧ xi≤beta/10 ∧ xi≤zeta ∧ etaE≤eta₀ ∧
      xi+24*etaE≤delta ∧ xi+6*etaE≤delta ∧ xi+3*((r:ℝ)+5)*etaE≤delta:=by
  let xi:=min (beta/20) (min (zeta/2) (delta/4))
  let den:ℝ:=12*((r:ℝ)+5)+96
  let etaE:=min (eta₀/2) (delta/den)
  have hr:0≤(r:ℝ):=Nat.cast_nonneg _
  have hden:0<den:=by dsimp [den];positivity
  have hxi:0<xi:=by dsimp [xi];positivity
  have heta:0<etaE:=by dsimp [etaE];positivity
  have hxib:xi≤beta/20:=min_le_left _ _
  have hxiz:xi≤zeta/2:=(min_le_right _ _).trans (min_le_left _ _)
  have hxid:xi≤delta/4:=(min_le_right _ _).trans (min_le_right _ _)
  have hetae:etaE≤eta₀/2:=min_le_left _ _
  have hetad:etaE≤delta/den:=min_le_right _ _
  have hmul:0≤(delta/den-etaE)*den:=mul_nonneg (sub_nonneg.mpr hetad) hden.le
  have hcancel:(delta/den)*den=delta:=div_mul_cancel₀ delta (ne_of_gt hden)
  have hrprod:0≤(r:ℝ)*etaE:=mul_nonneg hr heta.le
  dsimp only [den] at hmul hcancel
  refine ⟨xi,etaE,hxi,heta,?_,?_,?_,?_,?_,?_⟩ <;> nlinarith
end Oberwolfach
