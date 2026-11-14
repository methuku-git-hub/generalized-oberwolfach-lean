module

public import Oberwolfach.OrdinaryParentReferenceDeepJointChoice

@[expose] public section
/-! The same positive margins can be used by the parent profile, the
initial edit estimate and the later cleanup certificate. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_parent_cleanup_margin_choices
    (cBoundary cInitial ρ₀:ℝ) (hBoundary:0<cBoundary) (hInitial:0<cInitial) (hρ:0<ρ₀):
    ∃γ eParent hParent κ:ℝ,0<γ ∧ 0<eParent ∧ 0<hParent ∧ γ≤eParent ∧
      eParent≤cBoundary ∧ hParent≤cBoundary ∧ eParent≤cInitial ∧ hParent≤cInitial ∧
      0<κ ∧ κ≤1 ∧ κ≤ρ₀/8 :=by
  let γ:=min cBoundary cInitial/2
  let κ:=min (ρ₀/16) (1/2:ℝ)
  have hγ:0<γ:=by dsimp [γ];positivity
  have hγB:γ≤cBoundary:=by dsimp [γ];have hh:=min_le_left cBoundary cInitial;linarith
  have hγI:γ≤cInitial:=by dsimp [γ];have hh:=min_le_right cBoundary cInitial;linarith
  have hκ:0<κ:=by dsimp [κ];positivity
  have hκ1:κ≤1:=by dsimp [κ];have hh:=min_le_right (ρ₀/16) (1/2:ℝ);linarith
  have hκρ:κ≤ρ₀/8:=by dsimp [κ];have hh:=min_le_left (ρ₀/16) (1/2:ℝ);linarith
  exact ⟨γ,γ,γ,κ,hγ,hγ,hγ,le_rfl,hγB,hγB,hγI,hγI,hκ,hκ1,hκρ⟩
end Oberwolfach
