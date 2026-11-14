module

public import Oberwolfach.OrdinaryTriangleSameSpacingOuterInnerHost
public import Oberwolfach.OrdinaryTriangleNumericThresholdFromSelectedDomain

@[expose] public section
/-! One selected spacing serves the outer and inner events, parent weights
and the uniform wheel-certificate threshold before the host and sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000000
set_option maxRecDepth 16384
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_same_spacing_event_certificate
    (k d:ℕ) (hd:2≤d) (α ρ₀ pmin κ aLoad ε ξ b Bweight ηHub δ δcap capξ:ℝ)
    (βP ηP ηH βH cParent Bparent χhost δref href χref betaCert:ℝ) (hp:0<pmin) (hδ:0<δ) (hα:0<α)
    (cInner CInner ηInner eParent hParent ηend εf εrows othercap:ℝ)
    (ξInner Kdom BInner tHub eEvent hEvent capInner γold κold δInner tpot lamInner bold Bold:ℝ)
    (hselected:OrdinaryTriangleInnerSelectedNumericDomain α cInner CInner ε ρ₀ pmin ηInner eParent hParent (ρ₀/8) ηend εf εrows othercap
      ξInner Kdom BInner tHub eEvent hEvent capInner γold κold δInner tpot lamInner bold Bold betaCert)
    (hβchoose:∀betaCap:ℝ,0<betaCap→∃β:ℝ,0<β ∧ β≤1/4 ∧ β≤α/8 ∧ β≤κ ∧ β≤capξ ∧ β≤betaCap ∧ ξ+2*β<ηHub)
    (htri:OrdinaryTriangleHubAfterCapBeforeFailure d hd α ρ₀ pmin κ aLoad ε ξ b Bweight ηHub δ δcap)
    (εR εH χdeep χHub χone χtwo χcut:ℝ) (hεR:0<εR) (hεH:0<εH) (hχdeep:0<χdeep) (hχHub:0<χHub)
    (hχone:0<χone) (hχtwo:0<χtwo) (hχcut:0<χcut)
    (χinner χendpoint:ℝ) (hχinner:0<χinner) (hχendpoint:0<χendpoint)
    (hparentSelected:∃εTri:ℝ,0<εTri ∧
      ∃Mhost Mcut:ℕ,1≤Mhost ∧ 1≤Mcut ∧
        OrdinaryTriangleFixedDomainSelector k d Mhost hd (max (1/2) (cycleThreshold 3)) α pmin (ρ₀/16)
          βP ηP ηH βH cParent Bparent εTri ε χhost (2*(3*d)) hp ∧
        OrdinaryReferenceCutsDomainSelector d Mcut hd α pmin (ρ₀/16) δref href ε χref (2*(3*d)))
    (hk:4≤k) (hε:0<ε) (hεsmall:ε<1/4) (hρ:0<ρ₀)
    (ω βout bRoot BRoot hpack δpack εstar cLinear ζfresh:ℝ)
    (p βeGeo βhGeo ν cap εsup δsample τ eps ellCap:ℝ)
    (hfixed:OrdinaryTriangleRootFreeActualCoverAfterCleanup α k ω βout bRoot BRoot hpack δpack εstar cLinear (ρ₀/8) pmin
      cInner (4*CInner/pmin^7) εf ηInner ηend ζfresh εrows p βeGeo βhGeo ν cap εsup δsample τ)
    (heps:0<eps) (hp0:0<p) (hp1:p≤1) (hτ:0≤τ) (hζfresh:0<ζfresh)
    (hεsup:εsup≤p^2/4) (hsupport:τ+ν≤p^2/4)
    (hclass:τ+ν+(p*ellCap+δsample)≤ζfresh*(min (pmin^4/32) (endpointCountCoefficient pmin (ρ₀/8)/4)/4)*ε*p/4)
    (hblock:ν+cap≤ζfresh*(min (pmin^4/32) (endpointCountCoefficient pmin (ρ₀/8)/4)/4)*ε*p/4)
    (hpκ:p≤4*(ζfresh*(min (pmin^4/32) (endpointCountCoefficient pmin (ρ₀/8)/4)/4)*ε))
    (hsqrt:20*Real.sqrt (2*p)≤(ζfresh*(min (pmin^4/32) (endpointCountCoefficient pmin (ρ₀/8)/4)/4)*ε)/2)
    (Norder:ℕ) (horder:∀n:ℕ,Norder≤n→
      2≤(ζfresh*(min (pmin^4/32) (endpointCountCoefficient pmin (ρ₀/8)/4)/4)*ε)*p*n/4):
    ∃εTri β:ℝ,0<εTri ∧ 0<β ∧ β≤1/4 ∧ β≤α/8 ∧ β≤α/4 ∧ β≤κ ∧ β≤capξ ∧ β≤δ ∧ β≤εTri ∧ β≤betaCert ∧ ξ+2*β<ηHub ∧ ξInner+2*β<ηInner ∧ β≤2*δInner*(ρ₀/8)*pmin ∧
    ∃v₀ Mhost Mcut:ℕ,1≤v₀ ∧ 1≤Mhost ∧ 1≤Mcut ∧
      OrdinaryTriangleHubAfterSpacing d v₀ hd α ρ₀ pmin κ aLoad ε ξ b Bweight ηHub δcap εR εH χdeep χHub χone χtwo χcut β ∧
      OrdinaryTriangleFixedDomainSelector k d Mhost hd (max (1/2) (cycleThreshold 3)) α pmin (ρ₀/16)
        βP ηP ηH βH cParent Bparent εTri ε χhost (2*(3*d)) hp ∧
      OrdinaryReferenceCutsDomainSelector d Mcut hd α pmin (ρ₀/16) δref href ε χref (2*(3*d)) ∧
    ∃vInner:ℕ,1≤vInner ∧
      OrdinaryTriangleInnerEndpointHostSelector α cInner CInner ε ρ₀ pmin ξInner cInner BInner ηInner Kdom
        eParent hParent capInner χinner χendpoint tpot d hd β vInner ∧
    ∃M vCert vCommon:ℕ,64≤M ∧ 1≤vCert ∧ v₀≤vCommon ∧ vInner≤vCommon ∧ vCert≤vCommon ∧
      OrdinaryTriangleNumericCoreAfterThreshold β ε ρ₀ α pmin εrows tpot lamInner d k
        ω βout bRoot BRoot hpack δpack εstar cLinear cInner (4*CInner/pmin^7) ηInner
        p βeGeo βhGeo ν cap τ eps ellCap M vCert :=by
  obtain ⟨εTri,β,hεTri,hβ,hβ1,hβα8,hβα4,hβκ,hβcap,hβδ,hβtri,hβcert,hgap,hgapInner,hβbalance,
      v₀,Mhost,Mcut,hv₀,hMhost,hMcut,hafter,hselector,hcuts,vInner,hvInner,hInner⟩:=
    ordinary_triangle_same_spacing_outer_inner_host k d hd α ρ₀ pmin κ aLoad ε ξ b Bweight ηHub δ δcap capξ
      βP ηP ηH βH cParent Bparent χhost δref href χref betaCert hp hδ hα
      cInner CInner ηInner eParent hParent (ρ₀/8) ηend εf εrows othercap
      ξInner Kdom BInner tHub eEvent hEvent capInner γold κold δInner tpot lamInner bold Bold
      hselected hβchoose htri εR εH χdeep χHub χone χtwo χcut hεR hεH hχdeep hχHub hχone hχtwo hχcut
      χinner χendpoint hχinner hχendpoint hparentSelected
  obtain ⟨M,vCert,hM,hvCert,hcert⟩:=ordinary_triangle_numeric_threshold_from_selected_domain
    α cInner CInner ε ρ₀ pmin ηInner eParent hParent ηend εf εrows othercap
    ξInner Kdom BInner tHub eEvent hEvent capInner γold κold δInner tpot lamInner bold Bold betaCert
    hselected β hβ.le hβcert hε hεsmall hρ hα hp d k hk
    ω βout bRoot BRoot hpack δpack εstar cLinear ζfresh p βeGeo βhGeo ν cap εsup δsample τ eps
    hfixed heps hp0 hp1 hτ hζfresh hεsup hsupport ellCap hclass hblock hpκ hsqrt Norder horder
  exact ⟨εTri,β,hεTri,hβ,hβ1,hβα8,hβα4,hβκ,hβcap,hβδ,hβtri,hβcert,hgap,hgapInner,hβbalance,
    v₀,Mhost,Mcut,hv₀,hMhost,hMcut,hafter,hselector,hcuts,vInner,hvInner,hInner,
    M,vCert,max v₀ (max vInner vCert),hM,hvCert,le_max_left _ _,
    (le_max_left _ _).trans (le_max_right _ _),(le_max_right _ _).trans (le_max_right _ _),hcert⟩
end Oberwolfach
