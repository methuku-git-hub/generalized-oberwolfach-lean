module

public import Mathlib.Tactic

@[expose] public section
/-! The packing tolerance is chosen after spacing but below both the local
rate and an earlier ambient cap, while meeting the matching lower bound. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_relative_spacing_packing_choice
    (βfinal s κCap θ:ℝ) (hβ:0<βfinal) (hs:0<s) (hcap:0<κCap) (hθ:0<θ)
    (hrelative:θ≤(βfinal/80)*s) (habsolute:θ≤(βfinal/80)*κCap):
    ∃κ:ℝ,0<κ ∧ κ≤s/2 ∧ κ≤κCap/2 ∧ 10*θ≤κ*(βfinal/4) :=by
  let κ:=40*θ/βfinal
  have hκ:0<κ:=by dsimp [κ];positivity
  have hκs:κ≤s/2:=by
    dsimp [κ]
    apply (div_le_iff₀ hβ).2
    nlinarith only [hrelative]
  have hκcap:κ≤κCap/2:=by
    dsimp [κ]
    apply (div_le_iff₀ hβ).2
    nlinarith only [habsolute]
  have hκlower:10*θ≤κ*(βfinal/4):=by
    dsimp [κ]
    have hne:βfinal≠0:=ne_of_gt hβ
    field_simp
    norm_num
  exact ⟨κ,hκ,hκs,hκcap,hκlower⟩
end Oberwolfach
