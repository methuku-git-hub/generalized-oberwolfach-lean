module

public import Oberwolfach.OrdinaryParentReferenceCompatibleChoice

@[expose] public section
/-! Select the root-reference tolerances below the already fixed certificate
tolerance, retaining a positive gap for the later geometry. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_reference_certificate_gap_choices
    (εCert h ηcap gapcap ζlimit:ℝ) (hε:0<εCert) (hh:0<h) (hηcap:0<ηcap) (hgapcap:0<gapcap) (hζ:0<ζlimit):
    ∃ηH gap ζcap geomGap:ℝ,0<ηH ∧ ηH≤ηcap ∧ 0<gap ∧ gap≤gapcap ∧
      0<ζcap ∧ ζcap≤h ∧ ζcap≤ζlimit ∧ 2*ηH+gap<εCert ∧
      0<geomGap ∧ (2*ηH+gap)+geomGap=εCert :=by
  let ηH:=min (εCert/16) (ηcap/2)
  let gap:=min (εCert/4) (gapcap/2)
  let ζcap:=min (h/2) (ζlimit/2)
  let geomGap:=εCert-(2*ηH+gap)
  have hη:0<ηH:=by dsimp [ηH];positivity
  have hηE:ηH≤εCert/16:=min_le_left _ _
  have hηC:ηH≤ηcap/2:=min_le_right _ _
  have hgap:0<gap:=by dsimp [gap];positivity
  have hgapE:gap≤εCert/4:=min_le_left _ _
  have hgapC:gap≤gapcap/2:=min_le_right _ _
  have hζcap:0<ζcap:=by dsimp [ζcap];positivity
  have hζh:ζcap≤h/2:=min_le_left _ _
  have hζl:ζcap≤ζlimit/2:=min_le_right _ _
  have hcompat:2*ηH+gap<εCert:=by linarith
  exact ⟨ηH,gap,ζcap,geomGap,hη,by linarith,hgap,by linarith,hζcap,by linarith,by linarith,hcompat,by dsimp [geomGap];linarith,by dsimp [geomGap];ring⟩
end Oberwolfach
