module

public import Oberwolfach.OrdinaryActualCertificateGeometryStaticAt
public import Oberwolfach.OrdinaryActualCertificateReferenceStaticAt
public import Oberwolfach.OrdinaryParentDeepCutScaleChoices

@[expose] public section
/-! Instantiate the certificate geometry with the selected parent reference
and the previously selected deep-event constants. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_parent_deep_certificate_geometry_quarter
    (m loadK k:ℕ) (hm:3≤m) (α ρ₀ pstar βH c B δ h εCert cCert:ℝ)
    (hρ₀:0<ρ₀) (hp:0<pstar) (hβH:0<βH) (hc:0<c) (hB:0<B) (hδ:0<δ) (hδ1:δ<1/4) (hh:0<h)
    (ηH gap geomGap aDeep ρdeep θdeep ηProfile αcut:ℝ)
    (hη:0<ηH) (hgap:0<gap) (hgeomGap:0<geomGap) (hgeomEq:(2*ηH+gap)+geomGap=εCert)
    (ha:0<aDeep) (hρdeep:0<ρdeep) (hθdeep:0<θdeep) (hprofile:0<ηProfile) (hαcut:0<αcut)
    (hcert:OrdinaryActualCertificateReferenceStaticAt m loadK k hm α (βH/4) (ρ₀/16)
      (c*(1-δ)^((m+1)-1)) (B/((ρ₀/16)*pstar^(2*(m+1)-1))) (h/2) (δ/2) εCert cCert):
    ∃href δlimit geomCap:ℝ,0<href ∧ href≤αcut*pstar/64 ∧
      0<δlimit ∧ δlimit≤min (αcut/32) (pstar/512) ∧ 0<geomCap ∧ 2*geomCap≤h/2 ∧
      OrdinaryActualCertificateGeometryStaticAt m loadK k hm α (βH/4) (ρ₀/16)
        (c*(1-δ)^((m+1)-1)) (B/((ρ₀/16)*pstar^(2*(m+1)-1))) (h/2) (δ/2) εCert cCert
        ρ₀ pstar href δlimit aDeep ρdeep θdeep pstar ηProfile
        (c*(1-δ)^((m+1)-1)) (B/((ρ₀/16)*pstar^(2*(m+1)-1))) (2*ηH+gap) geomGap geomCap :=by
  obtain ⟨href,δlimit,geomCap,hhref,hhrefBound,hδlimit,hδlimitBound,hgeomCap,hgeomCapBound⟩:=
    ordinary_parent_deep_cut_scale_choices αcut pstar h hαcut hp hh
  have hb:0<c*(1-δ)^((m+1)-1):=mul_pos hc (pow_pos (by linarith) _)
  have hBroot:0<B/((ρ₀/16)*pstar^(2*(m+1)-1)):=by positivity
  refine ⟨href,δlimit,geomCap,hhref,hhrefBound,hδlimit,hδlimitBound,hgeomCap,hgeomCapBound,?_⟩
  exact hcert ρ₀ pstar href δlimit aDeep ρdeep θdeep pstar ηProfile
    (c*(1-δ)^((m+1)-1)) (B/((ρ₀/16)*pstar^(2*(m+1)-1))) (2*ηH+gap) geomGap geomCap
    hρ₀ hp hhref hδlimit ha hρdeep hθdeep hp hprofile hb hBroot.le hgeomGap hgeomCap
end Oberwolfach
