module

public import Oberwolfach.OrdinaryTriangleInnerSelectedNumericDomain
public import Oberwolfach.OrdinaryTriangleNumericCoreThresholdSelection

@[expose] public section
/-! The earlier inner numeric selection and its shared spacing cap directly
supply the uniform triangle certificate threshold before the host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_numeric_threshold_from_selected_domain
    (α c C ε ρ₀ pmin ηhub eParent hParent ηend εf εrows othercap:ℝ)
    (ξ Kdom Binner tHub eEvent hEvent capHub γold κold δInner tpot lamInner bold Bold βcap:ℝ)
    (hselected:OrdinaryTriangleInnerSelectedNumericDomain α c C ε ρ₀ pmin ηhub eParent hParent (ρ₀/8) ηend εf εrows othercap
      ξ Kdom Binner tHub eEvent hEvent capHub γold κold δInner tpot lamInner bold Bold βcap)
    (β:ℝ) (hβ:0≤β) (hβcap:β≤βcap) (hε:0<ε) (hε1:ε<1/4) (hρ₀:0<ρ₀) (hα:0<α) (hpmin:0<pmin)
    (d k:ℕ) (hk:4≤k)
    (ω βout b Bweight hpack δpack εstar cLinear ζfresh:ℝ)
    (p βeGeo βhGeo ν cap εsup δsample τ eps:ℝ)
    (hfixed:OrdinaryTriangleRootFreeActualCoverAfterCleanup α k ω βout b Bweight hpack δpack εstar cLinear (ρ₀/8) pmin
      c (4*C/pmin^7) εf ηhub ηend ζfresh εrows p βeGeo βhGeo ν cap εsup δsample τ)
    (heps:0<eps) (hp:0<p) (hp1:p≤1) (hτ:0≤τ) (hζfresh:0<ζfresh)
    (hεsup:εsup≤p^2/4) (hsupport:τ+ν≤p^2/4) (ellCap:ℝ)
    (hclass:τ+ν+(p*ellCap+δsample)≤ζfresh*(min (pmin^4/32) (endpointCountCoefficient pmin (ρ₀/8)/4)/4)*ε*p/4)
    (hblock:ν+cap≤ζfresh*(min (pmin^4/32) (endpointCountCoefficient pmin (ρ₀/8)/4)/4)*ε*p/4)
    (hpκ:p≤4*(ζfresh*(min (pmin^4/32) (endpointCountCoefficient pmin (ρ₀/8)/4)/4)*ε))
    (hsqrt:20*Real.sqrt (2*p)≤(ζfresh*(min (pmin^4/32) (endpointCountCoefficient pmin (ρ₀/8)/4)/4)*ε)/2)
    (Norder:ℕ) (horder:∀n:ℕ,Norder≤n→
      2≤(ζfresh*(min (pmin^4/32) (endpointCountCoefficient pmin (ρ₀/8)/4)/4)*ε)*p*n/4):
    ∃M v₀:ℕ,64≤M ∧ 1≤v₀ ∧
      OrdinaryTriangleNumericCoreAfterThreshold β ε ρ₀ α pmin εrows tpot lamInner d k
        ω βout b Bweight hpack δpack εstar cLinear c (4*C/pmin^7) ηhub p βeGeo βhGeo ν cap τ eps ellCap M v₀ :=by
  obtain ⟨_hξ,_hξη,_hK,_hB,_ht,_he,_hh,_hc,_heP,_hhP,hKdom,_hsetup,hdeep,hinner,_hcap,_hother,hspacing⟩:=hselected
  obtain ⟨hβ1,hβα,_hgap,hβbalance⟩:=hspacing β hβ hβcap
  exact ordinary_triangle_numeric_core_threshold_selection β ε ρ₀ α pmin Kdom ηend εf γold κold δInner εrows tpot lamInner bold Bold
    hβ hβ1 hβα hε hε1 hρ₀ hα hpmin hKdom hdeep hinner hβbalance d k hk
    ω βout b Bweight hpack δpack εstar cLinear c (4*C/pmin^7) ηhub ζfresh p βeGeo βhGeo ν cap εsup δsample τ eps
    hfixed heps hp hp1 hτ hζfresh hεsup hsupport ellCap hclass hblock hpκ hsqrt Norder horder
end Oberwolfach
