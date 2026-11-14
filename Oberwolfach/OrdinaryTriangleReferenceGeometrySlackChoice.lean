module

public import Mathlib.Tactic

@[expose] public section
/-! Fix positive host and root errors after the packing threshold, leaving
strict slack for the nonroot static-geometry selector. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_reference_geometry_slack_choice
    (εstar ηHcap gapcap:ℝ) (hεstar:0<εstar) (hηcap:0<ηHcap) (hgapcap:0<gapcap):
    ∃ηH gap:ℝ,0<ηH ∧ ηH≤ηHcap ∧ 0<gap ∧ gap≤gapcap ∧ 2*ηH+gap<εstar :=by
  let ηH:ℝ:=min ηHcap (εstar/16)/2
  let gap:ℝ:=min gapcap (εstar/8)/2
  have hηH:0<ηH:=by dsimp [ηH];positivity
  have hgap:0<gap:=by dsimp [gap];positivity
  have hηcap':ηH≤ηHcap:=by have hh:=min_le_left ηHcap (εstar/16);dsimp [ηH];linarith
  have hgapcap':gap≤gapcap:=by have hh:=min_le_left gapcap (εstar/8);dsimp [gap];linarith
  have hηsmall:ηH≤εstar/32:=by have hh:=min_le_right ηHcap (εstar/16);dsimp [ηH];linarith
  have hgapsmall:gap≤εstar/16:=by have hh:=min_le_right gapcap (εstar/8);dsimp [gap];linarith
  exact ⟨ηH,gap,hηH,hηcap',hgap,hgapcap',by linarith⟩
end Oberwolfach
