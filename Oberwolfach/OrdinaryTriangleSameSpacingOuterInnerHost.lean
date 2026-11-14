module

public import Oberwolfach.OrdinaryTriangleReferenceParentInnerSameSpacing
public import Oberwolfach.OrdinaryTriangleInnerEndpointHostSelection

@[expose] public section
/-! After the failure allowances are fixed, one spacing serves the parent,
outer hub, inner hub and endpoint selectors before the host is chosen. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_same_spacing_outer_inner_host
    (k d:ℕ) (hd:2≤d) (α ρ₀ pmin κ aLoad ε ξ b Bweight ηHub δ δcap capξ:ℝ)
    (βP ηP ηH βH cParent Bparent χhost δref href χref betaCert:ℝ) (hp:0<pmin) (hδ:0<δ) (hα:0<α)
    (cInner CInner ηInner eParent hParent κe ηend εf εrows othercap:ℝ)
    (ξInner Kdom BInner tHub eEvent hEvent capInner γold κold δInner tpot lamInner bold Bold:ℝ)
    (hselected:OrdinaryTriangleInnerSelectedNumericDomain α cInner CInner ε ρ₀ pmin ηInner eParent hParent κe ηend εf εrows othercap
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
        OrdinaryReferenceCutsDomainSelector d Mcut hd α pmin (ρ₀/16) δref href ε χref (2*(3*d))):
    ∃εTri β:ℝ,0<εTri ∧ 0<β ∧ β≤1/4 ∧ β≤α/8 ∧ β≤α/4 ∧ β≤κ ∧ β≤capξ ∧ β≤δ ∧ β≤εTri ∧ β≤betaCert ∧ ξ+2*β<ηHub ∧ ξInner+2*β<ηInner ∧ β≤2*δInner*κe*pmin ∧
    ∃v₀ Mhost Mcut:ℕ,1≤v₀ ∧ 1≤Mhost ∧ 1≤Mcut ∧
      OrdinaryTriangleHubAfterSpacing d v₀ hd α ρ₀ pmin κ aLoad ε ξ b Bweight ηHub δcap εR εH χdeep χHub χone χtwo χcut β ∧
      OrdinaryTriangleFixedDomainSelector k d Mhost hd (max (1/2) (cycleThreshold 3)) α pmin (ρ₀/16)
        βP ηP ηH βH cParent Bparent εTri ε χhost (2*(3*d)) hp ∧
      OrdinaryReferenceCutsDomainSelector d Mcut hd α pmin (ρ₀/16) δref href ε χref (2*(3*d)) ∧
    ∃vInner:ℕ,1≤vInner ∧
      OrdinaryTriangleInnerEndpointHostSelector α cInner CInner ε ρ₀ pmin ξInner cInner BInner ηInner Kdom
        eParent hParent capInner χinner χendpoint tpot d hd β vInner :=by
  have hdomain:=hselected
  obtain ⟨_hξ,_hξη,_hK,_hB,_ht,_he,_hh,_hc,_heP,_hhP,_hKdom,hsetup,_hdeep,hinner,_hcap,_hother,_hspacing⟩:=hdomain
  obtain ⟨εTri,β,hεTri,hβ,hβ1,hβα8,hβα4,hβκ,hβcap,hβδ,hβtri,hβcert,hgap,hgapInner,hβbalance,
      v₀,Mhost,Mcut,hv₀,hMhost,hMcut,hafter,hselector,hcuts⟩:=
    ordinary_triangle_reference_parent_inner_same_spacing k d hd α ρ₀ pmin κ aLoad ε ξ b Bweight ηHub δ δcap capξ
      βP ηP ηH βH cParent Bparent χhost δref href χref betaCert hp hδ hα
      cInner CInner ηInner eParent hParent κe ηend εf εrows othercap
      ξInner Kdom BInner tHub eEvent hEvent capInner γold κold δInner tpot lamInner bold Bold
      hselected hβchoose htri εR εH χdeep χHub χone χtwo χcut hεR hεH hχdeep hχHub hχone hχtwo hχcut hparentSelected
  obtain ⟨vInner,hvInner,hInner⟩:=ordinary_triangle_inner_endpoint_select_host_data α cInner CInner ε ρ₀ pmin ξInner
    cInner BInner ηInner Kdom eParent hParent capInner hsetup χinner hχinner d hd β hβ.le hβ1 hβα8 hgapInner
    tpot χendpoint hinner.t_pos hχendpoint
  exact ⟨εTri,β,hεTri,hβ,hβ1,hβα8,hβα4,hβκ,hβcap,hβδ,hβtri,hβcert,hgap,hgapInner,hβbalance,
    v₀,Mhost,Mcut,hv₀,hMhost,hMcut,hafter,hselector,hcuts,vInner,hvInner,hInner⟩
end Oberwolfach
