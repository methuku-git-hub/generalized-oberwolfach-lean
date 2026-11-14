module

public import Oberwolfach.OrdinaryParentReferenceFirstChoice
public import Oberwolfach.OrdinaryParentReferenceCompatibleChoices

@[expose] public section
/-! Fix the actual certificate tolerance using the selected parent weights,
then permit the parent error and gap to be chosen below that tolerance. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_parent_reference_compatible_choice
    (m loadK d:ℕ) (hm:3≤m) (hd:2≤d) (α ρ₀ pstar ηP:ℝ)
    (hα:0<α) (hα1:α≤1/2)
    (hθ1:max (1/2) (cycleThreshold (m+1))+α/2≤1)
    (hρ₀:0<ρ₀) (hp:0<pstar) (hp1:pstar≤1) (hηP:0<ηP):
    OrdinaryParentReferenceCompatibleChoices m loadK d hm hd α ρ₀ pstar ηP hp :=by
  obtain ⟨δ,h,βP,row,k,βH,c,B,εstar,cLinear,hδ,hδ1,hh,hβP,hrow,hk,hβH,hc,hB,hεstar,hcLinear,hrule,hAt,hparent⟩:=
    ordinary_parent_reference_first_choice m loadK d hm hd α ρ₀ pstar ηP hα hα1 hθ1 hρ₀ hp hp1 hηP
  have hbRoot:0<c*(1-δ)^((m+1)-1):=by
    exact mul_pos hc (pow_pos (by linarith) _)
  have hBRoot:0<B/((ρ₀/16)*pstar^(2*(m+1)-1)):=by positivity
  obtain ⟨εCert,cCert,hεCert,hcCert,hcert⟩:=hAt (βH/2) (ρ₀/16)
    (c*(1-δ)^((m+1)-1)) (B/((ρ₀/16)*pstar^(2*(m+1)-1))) (h/2) (δ/2)
    (by positivity) (by positivity) hbRoot hBRoot (by positivity) (by positivity) (by linarith)
  refine ⟨δ,h,βP,row,k,βH,c,B,εstar,cLinear,hδ,hδ1,hh,hβP,hrow,hk,hβH,hc,hB,hεstar,hcLinear,hrule,
    εCert,cCert,hεCert,hcCert,hcert,?_⟩
  intro ηH gap ζcap hη hgap hζ hζh hcompatible
  exact hparent ηH gap ζcap hη hgap hζ hζh
end Oberwolfach
