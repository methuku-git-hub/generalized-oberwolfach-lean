module

public import Oberwolfach.OrdinaryBoundaryFullSelectionScales

@[expose] public section
/-! The cleanup density and an arbitrary cap for its packing threshold can
be fixed before selecting the actual approximate packing. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_cleanup_cap_choice (p κ ζ:ℝ) (hp:0<p) (hκ:0<κ) (hζ:0<ζ):
    ∃ν cap:ℝ,0<ν ∧ 0<cap ∧ ν≤ζ*κ*p/4 ∧ ν≤p^2/16 ∧
      ∀τ:ℝ,0≤τ→τ≤cap→τ+ν≤p^2/4:=by
  let ν:=min (p^2/16) (ζ*κ*p/16)
  let cap:=p^2/8
  have hν:0<ν:=by dsimp [ν];positivity
  have hcap:0<cap:=by dsimp [cap];positivity
  have hνp:ν≤p^2/16:=min_le_left _ _
  have hνκ:ν≤ζ*κ*p/16:=min_le_right _ _
  refine ⟨ν,cap,hν,hcap,?_,hνp,?_⟩
  · have hh:0≤ζ*κ*p:=by positivity
    linarith only [hνκ,hh]
  · intro τ _ hτ
    dsimp [cap] at hτ
    nlinarith only [hτ,hνp,sq_nonneg p]
end Oberwolfach
