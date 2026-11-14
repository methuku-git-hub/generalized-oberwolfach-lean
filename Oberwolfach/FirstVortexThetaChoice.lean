module

public import Oberwolfach.FirstVortexLocalLoadMargins

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_theta_choice (δ θMax:ℝ) (hδ:0<δ) (hMax:0<θMax):
    ∃θ:ℝ,0<θ ∧ θ≤1/100 ∧ θ≤θMax ∧ θ≤δ/32 ∧ 10*θ≤δ :=by
  let θ:ℝ:=min θMax (min (1/100:ℝ) (δ/32))/2
  have hpos:0<θ:=by dsimp [θ]; positivity
  have hMaxBound:θ≤θMax:=by
    have h:=min_le_left θMax (min (1/100:ℝ) (δ/32))
    dsimp [θ]
    linarith
  have hOne:θ≤(1/100:ℝ):=by
    have h: min θMax (min (1/100:ℝ) (δ/32))≤(1/100:ℝ):=
      (min_le_right _ _).trans (min_le_left _ _)
    dsimp [θ]
    linarith
  have hDelta:θ≤δ/32:=by
    have h: min θMax (min (1/100:ℝ) (δ/32))≤δ/32:=
      (min_le_right _ _).trans (min_le_right _ _)
    dsimp [θ]
    linarith
  exact ⟨θ,hpos,hOne,hMaxBound,hDelta,by linarith⟩
end Oberwolfach
