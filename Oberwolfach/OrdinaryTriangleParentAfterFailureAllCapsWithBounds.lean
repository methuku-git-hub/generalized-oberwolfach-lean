module

public import Oberwolfach.OrdinaryTriangleParentAfterFailureChoice
public import Oberwolfach.OrdinaryTriangleHubLateSpacingWithBounds
public import Oberwolfach.OrdinaryTriangleReferenceEventHierarchy

@[expose] public section
/-! Choose one triangle vortex error and size after the parent selector's
failure-dependent cap is known. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_parent_after_failure_all_caps_with_bounds
    (k d:ℕ) (hd:2≤d) (α ρ₀ pmin κ aLoad ε ξ b Bweight ηHub δ δcap capξ:ℝ)
    (βP ηP ηH βH cParent Bparent χhost δref href χref betaCert:ℝ) (hp:0<pmin) (hδ:0<δ) (hbetaCert:0<betaCert)
    (hβchoose:∀betaCap:ℝ,0<betaCap→∃β:ℝ,0<β ∧ β≤1/4 ∧ β≤α/8 ∧ β≤κ ∧ β≤capξ ∧ β≤betaCap ∧ ξ+2*β<ηHub)
    (htri:OrdinaryTriangleHubAfterCapBeforeFailure d hd α ρ₀ pmin κ aLoad ε ξ b Bweight ηHub δ δcap)
    (εR εH χdeep χHub χone χtwo χcut:ℝ) (hεR:0<εR) (hεH:0<εH) (hχdeep:0<χdeep) (hχHub:0<χHub)
    (hχone:0<χone) (hχtwo:0<χtwo) (hχcut:0<χcut)
    (hparent:∃εTri βmax:ℝ,0<εTri ∧ 0<βmax ∧ βmax≤1/4 ∧ βmax≤α/4 ∧ βmax≤εTri ∧
      ∃Mhost Mcut:ℕ,1≤Mhost ∧ 1≤Mcut ∧
        OrdinaryTriangleFixedDomainSelector k d Mhost hd (max (1/2) (cycleThreshold 3)) α pmin (ρ₀/16)
          βP ηP ηH βH cParent Bparent εTri ε χhost (2*(3*d)) hp ∧
        OrdinaryReferenceCutsDomainSelector d Mcut hd α pmin (ρ₀/16) δref href ε χref (2*(3*d))):
    ∃εTri β:ℝ,0<εTri ∧ 0<β ∧ β≤1/4 ∧ β≤α/8 ∧ β≤α/4 ∧ β≤κ ∧ β≤capξ ∧ β≤δ ∧ β≤εTri ∧ β≤betaCert ∧ ξ+2*β<ηHub ∧
    ∃v₀ Mhost Mcut:ℕ,1≤v₀ ∧ 1≤Mhost ∧ 1≤Mcut ∧
      OrdinaryTriangleHubAfterSpacing d v₀ hd α ρ₀ pmin κ aLoad ε ξ b Bweight ηHub δcap εR εH χdeep χHub χone χtwo χcut β ∧
      OrdinaryTriangleFixedDomainSelector k d Mhost hd (max (1/2) (cycleThreshold 3)) α pmin (ρ₀/16)
        βP ηP ηH βH cParent Bparent εTri ε χhost (2*(3*d)) hp ∧
      OrdinaryReferenceCutsDomainSelector d Mcut hd α pmin (ρ₀/16) δref href ε χref (2*(3*d)) :=by
  obtain ⟨εTri,βmax,hεTri,hβmax,hβmax1,hβmaxα,hβmaxTri,Mhost,Mcut,hMhost,hMcut,hselector,hcuts⟩:=hparent
  obtain ⟨β,hβ,hβ1,hβα8,hβκ,hβcap,hβδ,hβmax',hgap,v₀,hv₀,hafter⟩:=ordinary_triangle_hub_late_spacing_with_bounds d hd α ρ₀ pmin κ aLoad ε ξ b Bweight ηHub δ δcap capξ
    hδ hβchoose htri εR εH χdeep χHub χone χtwo χcut hεR hεH hχdeep hχHub hχone hχtwo hχcut (min βmax betaCert) (by positivity)
  have hβparent:β≤βmax:=hβmax'.trans (min_le_left _ _)
  have hβcert:β≤betaCert:=hβmax'.trans (min_le_right _ _)
  exact ⟨εTri,β,hεTri,hβ,hβ1,hβα8,hβparent.trans hβmaxα,hβκ,hβcap,hβδ,hβparent.trans hβmaxTri,hβcert,hgap,
    v₀,Mhost,Mcut,hv₀,hMhost,hMcut,hafter,hselector,hcuts⟩
end Oberwolfach
