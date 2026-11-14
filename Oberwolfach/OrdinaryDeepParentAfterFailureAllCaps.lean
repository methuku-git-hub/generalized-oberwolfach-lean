module

public import Oberwolfach.OrdinaryDeepParentAfterFailureChoice
public import Oberwolfach.OrdinaryParentJointReferenceChoices

@[expose] public section
/-! Once the failure allowances are fixed, use the parent selector's actual
cap for the same vortex error and choose one terminal threshold. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach

theorem ordinary_deep_parent_after_failure_all_caps
    (m K k d:ℕ) (hm:3≤m) (hd:2≤d) (α ρ₀ pmin αcut c C a ε₀ ρ θdeep:ℝ)
    (aLoad ε ξ b Bweight ηHub Kdom χinner χdeep eParent hParent εR εH χone χtwo χcut cap capξ:ℝ)
    (βP ηP row ηH βH cParent Bparent χhost δref href χref betaCert:ℝ) (hp:0<pmin) (hbetaCert:0<betaCert)
    (hβchoose:∀betaCap:ℝ,0<betaCap→∃β:ℝ,0<β ∧ β≤1/4 ∧ β≤α/8 ∧ β≤ε₀ ∧ β≤capξ ∧ β≤betaCap ∧ ξ+2*β<ηHub)
    (hdeep:OrdinaryDeepRowsCutsAfterParameters m K α ρ₀ pmin αcut c C a ε₀ ρ θdeep aLoad ε ξ b Bweight ηHub Kdom χinner χdeep eParent hParent εR εH χone χtwo χcut cap)
    (hparent:∃εTri βmax:ℝ,0<εTri ∧ 0<βmax ∧ βmax≤1/4 ∧ βmax≤α/4 ∧ βmax≤εTri ∧
      ∃Mhost Mcut:ℕ,1≤Mhost ∧ 1≤Mcut ∧
        OrdinaryGeneralFixedDomainSelector m k d Mhost hm hd (max (1/2) (cycleThreshold (m+1))) α pmin (ρ₀/16)
          βP ηP row ηH βH cParent Bparent εTri ε χhost (2*(3*d)) hp ∧
        OrdinaryReferenceCutsDomainSelector d Mcut hd α pmin (ρ₀/16) δref href ε χref (2*(3*d))):
    ∃εTri β:ℝ,0<εTri ∧ 0<β ∧ β≤1/4 ∧ β≤α/4 ∧ β≤εTri ∧ β≤betaCert ∧
    ∃v₀ Mhost Mcut:ℕ,1≤v₀ ∧ 1≤Mhost ∧ 1≤Mcut ∧
      OrdinaryDeepRowsCutsAfterSpacing m K d hd v₀ β α ρ₀ pmin αcut c C a ε₀ ρ θdeep aLoad ε ξ b Bweight ηHub Kdom χinner χdeep eParent hParent εR εH χone χtwo χcut cap ∧
      OrdinaryGeneralFixedDomainSelector m k d Mhost hm hd (max (1/2) (cycleThreshold (m+1))) α pmin (ρ₀/16)
        βP ηP row ηH βH cParent Bparent εTri ε χhost (2*(3*d)) hp ∧
      OrdinaryReferenceCutsDomainSelector d Mcut hd α pmin (ρ₀/16) δref href ε χref (2*(3*d)) :=by
  obtain ⟨εTri,βmax,hεTri,hβmax,hβmax1,hβmaxα,hβmaxTri,Mhost,Mcut,hMhost,hMcut,hselector,hcuts⟩:=hparent
  obtain ⟨β,hβ,hβmax',v₀,hv₀,hafter⟩:=ordinary_deep_rows_cuts_late_spacing m K α ρ₀ pmin αcut c C a ε₀ ρ θdeep
    aLoad ε ξ b Bweight ηHub Kdom χinner χdeep eParent hParent εR εH χone χtwo χcut cap capξ hβchoose hdeep d hd (min βmax betaCert) (by positivity)
  have hβparent:β≤βmax:=hβmax'.trans (min_le_left _ _)
  have hβcert:β≤betaCert:=hβmax'.trans (min_le_right _ _)
  exact ⟨εTri,β,hεTri,hβ,hβparent.trans hβmax1,hβparent.trans hβmaxα,hβparent.trans hβmaxTri,hβcert,
    v₀,Mhost,Mcut,hv₀,hMhost,hMcut,hafter,hselector,hcuts⟩
end Oberwolfach
