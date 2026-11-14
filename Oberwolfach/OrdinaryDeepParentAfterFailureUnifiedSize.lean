module

public import Oberwolfach.OrdinaryDeepParentAfterFailureCertificateCaps
public import Oberwolfach.OrdinaryUnifiedVortexSizeChoice
public import Oberwolfach.OrdinaryVortexCertificateBetaCap
public import Oberwolfach.OrdinaryParentJointReferenceChoices

@[expose] public section
/-! Once the failure allowances are fixed, use the parent selector's actual
cap for the same vortex error and choose one terminal threshold. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach

theorem ordinary_deep_parent_after_failure_unified_size
    (m K k d:ℕ) (hm:3≤m) (hd:2≤d) (α ρ₀ pmin αcut c C a ε₀ ρ θdeep:ℝ)
    (aLoad ε ξ b Bweight ηHub Kdom χinner χdeep eParent hParent εR εH χone χtwo χcut cap capξ:ℝ)
    (βP ηP row ηH βH cParent Bparent χhost δref href χref βcap δInitial δDeep δedit:ℝ) (hp:0<pmin)
    (hβcap:0<βcap) (hδInitial:0<δInitial) (hδDeep:0<δDeep) (hδedit:0<δedit)
    (hεpos:0<ε) (m₀ Nmin:ℕ)
    (hβchoose:∀betaCap:ℝ,0<betaCap→∃β:ℝ,0<β ∧ β≤1/4 ∧ β≤α/8 ∧ β≤ε₀ ∧ β≤capξ ∧ β≤betaCap ∧ ξ+2*β<ηHub)
    (hdeep:OrdinaryDeepRowsCutsAfterParameters m K α ρ₀ pmin αcut c C a ε₀ ρ θdeep aLoad ε ξ b Bweight ηHub Kdom χinner χdeep eParent hParent εR εH χone χtwo χcut cap)
    (hparent:∃εTri βmax:ℝ,0<εTri ∧ 0<βmax ∧ βmax≤1/4 ∧ βmax≤α/4 ∧ βmax≤εTri ∧
      ∃Mhost Mcut:ℕ,1≤Mhost ∧ 1≤Mcut ∧
        OrdinaryGeneralFixedDomainSelector m k d Mhost hm hd (max (1/2) (cycleThreshold (m+1))) α pmin (ρ₀/16)
          βP ηP row ηH βH cParent Bparent εTri ε χhost (2*(3*d)) hp ∧
        OrdinaryReferenceCutsDomainSelector d Mcut hd α pmin (ρ₀/16) δref href ε χref (2*(3*d))):
    ∃εTri β:ℝ,0<εTri ∧ 0<β ∧ β≤1/4 ∧ β≤α/4 ∧ β≤εTri ∧ β≤βcap ∧ β≤δInitial ∧ β≤δDeep ∧ β≤δedit ∧
    ∃v₀ Mhost Mcut N mv:ℕ,1≤v₀ ∧ 1≤Mhost ∧ 1≤Mcut ∧
      Nmin≤N ∧ 2/ε≤(N:ℝ) ∧ 1≤mv ∧ v₀≤mv ∧ m₀≤mv ∧
      (N:ℝ)≤ε*mv/2 ∧ (Mhost:ℝ)≤ε*mv/2 ∧ (Mcut:ℝ)≤ε*mv/2 ∧
      OrdinaryDeepRowsCutsAfterSpacing m K d hd v₀ β α ρ₀ pmin αcut c C a ε₀ ρ θdeep aLoad ε ξ b Bweight ηHub Kdom χinner χdeep eParent hParent εR εH χone χtwo χcut cap ∧
      OrdinaryGeneralFixedDomainSelector m k d Mhost hm hd (max (1/2) (cycleThreshold (m+1))) α pmin (ρ₀/16)
        βP ηP row ηH βH cParent Bparent εTri ε χhost (2*(3*d)) hp ∧
      OrdinaryReferenceCutsDomainSelector d Mcut hd α pmin (ρ₀/16) δref href ε χref (2*(3*d)) :=by
  obtain ⟨εTri,β,hεTri,hβ,hβ1,hβα,hβTri,hβcap,hβInitial,hβDeep,hβedit,v₀,Mhost,Mcut,hv₀,hMhost,hMcut,hafter,hselector,hcuts⟩:=
    ordinary_deep_parent_after_failure_certificate_caps m K k d hm hd α ρ₀ pmin αcut c C a ε₀ ρ θdeep
      aLoad ε ξ b Bweight ηHub Kdom χinner χdeep eParent hParent εR εH χone χtwo χcut cap capξ
      βP ηP row ηH βH cParent Bparent χhost δref href χref βcap δInitial δDeep δedit hp hβcap hδInitial hδDeep hδedit hβchoose hdeep hparent
  obtain ⟨N,mv,hNmin,hNε,hmv,hvsize,hmsize,hNsize,hhostsize,hcutsize⟩:=
    ordinary_unified_vortex_size_choice ε hεpos v₀ m₀ Nmin Mhost Mcut
  exact ⟨εTri,β,hεTri,hβ,hβ1,hβα,hβTri,hβcap,hβInitial,hβDeep,hβedit,
    v₀,Mhost,Mcut,N,mv,hv₀,hMhost,hMcut,hNmin,hNε,hmv,hvsize,hmsize,hNsize,hhostsize,hcutsize,hafter,hselector,hcuts⟩
end Oberwolfach
