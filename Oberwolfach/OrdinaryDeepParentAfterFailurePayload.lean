module

public import Oberwolfach.OrdinaryDeepParentSizeAfterBeta
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

theorem ordinary_deep_parent_after_failure_payload
    (m K k d:ℕ) (hm:3≤m) (hd:2≤d) (α ρ₀ pmin αcut c C a ε₀ ρ θdeep:ℝ)
    (aLoad ε ξ b Bweight ηHub Kdom χinner χdeep eParent hParent εR εH χone χtwo χcut cap capξ:ℝ)
    (βP ηP row ηH βH cParent Bparent χhost δref href χref βcap δInitial δDeep δedit:ℝ) (hp:0<pmin)
    (hβcap:0<βcap) (hδInitial:0<δInitial) (hδDeep:0<δDeep) (hδedit:0<δedit)
    (hεpos:0<ε)
    (Payload:ℝ→ℕ→ℕ→Prop)
    (hPayload:∀β:ℝ,0<β→β≤1/4→β≤βcap→β≤δInitial→β≤δDeep→β≤δedit→∃m₀ Nmin:ℕ,Payload β m₀ Nmin)
    (hβchoose:∀betaCap:ℝ,0<betaCap→∃β:ℝ,0<β ∧ β≤1/4 ∧ β≤α/8 ∧ β≤ε₀ ∧ β≤capξ ∧ β≤betaCap ∧ ξ+2*β<ηHub)
    (hdeep:OrdinaryDeepRowsCutsAfterParameters m K α ρ₀ pmin αcut c C a ε₀ ρ θdeep aLoad ε ξ b Bweight ηHub Kdom χinner χdeep eParent hParent εR εH χone χtwo χcut cap)
    (hparent:∃εTri βmax:ℝ,0<εTri ∧ 0<βmax ∧ βmax≤1/4 ∧ βmax≤α/4 ∧ βmax≤εTri ∧
      ∃Mhost Mcut:ℕ,1≤Mhost ∧ 1≤Mcut ∧
        OrdinaryGeneralFixedDomainSelector m k d Mhost hm hd (max (1/2) (cycleThreshold (m+1))) α pmin (ρ₀/16)
          βP ηP row ηH βH cParent Bparent εTri ε χhost (2*(3*d)) hp ∧
        OrdinaryReferenceCutsDomainSelector d Mcut hd α pmin (ρ₀/16) δref href ε χref (2*(3*d))):
    ∃εTri β:ℝ,0<εTri ∧ 0<β ∧ β≤1/4 ∧ β≤α/4 ∧ β≤εTri ∧ β≤βcap ∧ β≤δInitial ∧ β≤δDeep ∧ β≤δedit ∧
    ∃v₀ Mhost Mcut:ℕ,1≤v₀ ∧ 1≤Mhost ∧ 1≤Mcut ∧
      OrdinaryDeepRowsCutsAfterSpacing m K d hd v₀ β α ρ₀ pmin αcut c C a ε₀ ρ θdeep aLoad ε ξ b Bweight ηHub Kdom χinner χdeep eParent hParent εR εH χone χtwo χcut cap ∧
      OrdinaryGeneralFixedDomainSelector m k d Mhost hm hd (max (1/2) (cycleThreshold (m+1))) α pmin (ρ₀/16)
        βP ηP row ηH βH cParent Bparent εTri ε χhost (2*(3*d)) hp ∧
      OrdinaryReferenceCutsDomainSelector d Mcut hd α pmin (ρ₀/16) δref href ε χref (2*(3*d)) ∧
      ∃m₀ Nmin:ℕ,Payload β m₀ Nmin ∧ ∃N mv:ℕ,Nmin≤N ∧ 2/ε≤(N:ℝ) ∧ 1≤mv ∧ v₀≤mv ∧ m₀≤mv ∧
        (N:ℝ)≤ε*mv/2 ∧ (Mhost:ℝ)≤ε*mv/2 ∧ (Mcut:ℝ)≤ε*mv/2 :=by
  obtain ⟨εTri,β,hεTri,hβ,hβ1,hβα,hβTri,hβcap,hβInitial,hβDeep,hβedit,v₀,Mhost,Mcut,hv₀,hMhost,hMcut,hafter,hselector,hcuts,hsize⟩:=
    ordinary_deep_parent_size_after_beta m K k d hm hd α ρ₀ pmin αcut c C a ε₀ ρ θdeep
      aLoad ε ξ b Bweight ηHub Kdom χinner χdeep eParent hParent εR εH χone χtwo χcut cap capξ
      βP ηP row ηH βH cParent Bparent χhost δref href χref βcap δInitial δDeep δedit hp hβcap hδInitial hδDeep hδedit hεpos hβchoose hdeep hparent
  obtain ⟨m₀,Nmin,hpayload⟩:=hPayload β hβ hβ1 hβcap hβInitial hβDeep hβedit
  exact ⟨εTri,β,hεTri,hβ,hβ1,hβα,hβTri,hβcap,hβInitial,hβDeep,hβedit,
    v₀,Mhost,Mcut,hv₀,hMhost,hMcut,hafter,hselector,hcuts,m₀,Nmin,hpayload,hsize m₀ Nmin⟩
end Oberwolfach
