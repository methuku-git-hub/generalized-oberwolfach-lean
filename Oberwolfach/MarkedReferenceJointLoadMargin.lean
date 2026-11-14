module

public import Oberwolfach.MarkedJointLoadMargin

@[expose] public section
/-! The reference event's parent and local load errors can be made small
simultaneously, with the shared leading tolerances chosen only once. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
theorem marked_reference_joint_load_margin_choice (r:ℕ) (κ θ ρstar sstar Bload Kload:ℝ)
    (hκ:0<κ) (hθ:0<θ) (hρ:0<ρstar) (hs:0<sstar) (hB:0<Bload) (hK:0<Kload):
    let base:=(((r+4):ℝ)+1)^4*(2*Bload/(ρstar*sstar/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1));
    ∃ τ εLoad ζLoad ζLocal:ℝ,0<τ ∧ 0<εLoad ∧ 0<ζLoad ∧ 0<ζLocal ∧
      τ+εLoad+11*base*Kload*ζLoad≤κ/4 ∧
      τ+εLoad+5*base*Kload*ζLocal≤θ/4 := by
  intro base
  have hb:0≤base:=by dsimp [base];positivity
  obtain ⟨τ,ε,ζ,ζlocal,hτ,hε,hζ,hζlocal,hparent,hlocal⟩:=
    marked_joint_load_margin_choice κ θ (11*base*Kload) (5*base*Kload) hκ hθ (by positivity) (by positivity)
  exact ⟨τ,ε,ζ,ζlocal,hτ,hε,hζ,hζlocal,hparent,hlocal⟩
end Oberwolfach
