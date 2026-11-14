module

public import Oberwolfach.OrdinaryParentReferenceFirstStaticBeforeSpacing
public import Oberwolfach.OrdinaryJointActualCertificateReferenceFirstStatic
public import Oberwolfach.OrdinaryGeneralDeepReferenceCapacityBeforeSpacing

@[expose] public section
/-! The same parent wheel size supports the actual local certificate
hierarchy, the sharp reference scale and the later sampled selectors. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_parent_reference_first_static_choice
    (m loadK:ℕ) (hm:3≤m) (α ρ₀ pstar ηP:ℝ)
    (hα:0<α) (hα1:α≤1/2)
    (hθ1:max (1/2) (cycleThreshold (m+1))+α/2≤1)
    (hρ₀:0<ρ₀) (hp:0<pstar) (hp1:pstar≤1) (hηP:0<ηP):
    OrdinaryParentReferenceFirstStaticBeforeSpacing m loadK hm α ρ₀ pstar ηP hp :=by
  obtain ⟨Nroot,hjoint⟩:=ordinary_joint_actual_certificate_reference_first_static m loadK hm α hα
  obtain ⟨δ,h,βP,row,k,βH,c,B,εstar,cLinear,hδ,hδ1,hh,hβP,hrow,hk,hkmin,hβH,hc,hB,hεstar,hcLinear,hrule,hevents⟩:=
    ordinary_general_deep_reference_capacity_before_spacing Nroot m hm α ρ₀ pstar ηP hα hα1 hθ1 hρ₀ hp hp1 hηP
  have hk4:4≤k:=by omega
  refine ⟨δ,h,βP,row,k,βH,c,B,εstar,cLinear,hδ,hδ1,hh,hβP,hrow,hk,hβH,hc,hB,hεstar,hcLinear,hrule,hjoint k hkmin hk4,?_⟩
  intro ηH gap ζcap hηH hgap hζcap hζh
  obtain ⟨ζparent,rateParent,lamroot,hζparent,hrate,hlam,hζcap',N₀,hN₀,hscale,hroot⟩:=
    ordinary_general_fine_parent_root_scale_choice m loadK k hm (by omega) α βH ηH c B (ρ₀/16) pstar δ h gap ζcap
      hβH hηH hc.le hB.le (by positivity) hp hδ (by linarith) hh hgap hζcap hζh
  refine ⟨ζparent,rateParent,lamroot,hζparent,hrate,hlam,hζcap',N₀,hN₀,hscale,hroot,?_,?_⟩
  · intro rate hrate
    exact ordinary_general_edit_scale_rate_monotone (m+1) βH ηH B (ρ₀/16) pstar (βH/2) (2*ηH) ζparent rate rateParent N₀ hrate hscale
  · intro d hd ε χhost χcut hε hε1 hχhost hχcut
    exact hevents d hd ηH ε χhost χcut hηH hε hε1 hχhost hχcut
end Oberwolfach
