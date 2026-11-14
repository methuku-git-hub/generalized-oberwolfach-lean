module

public import Oberwolfach.OrdinaryParentRootPackingSlack
public import Oberwolfach.OrdinaryVortexFineCertificateAtGeneralLoad

@[expose] public section
/-! The selected parent margin and matching coefficient discharge the
packing and matching-cap inequalities for the common certificate record. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_selected_parent_certificate_bounds
    (s:OrdinaryVortexFineCertificateParametersGeneralLoad)
    (h ζparent geomCap ξreserve ζout ε cMatch θmatch:ℝ)
    (hsPack:s.hpack=h/2) (hζ:ζparent≤h) (hgeom:2*geomCap≤h/2)
    (hξ:ξreserve≤geomCap) (hout:ζout≤geomCap)
    (hε:0≤ε) (hθ:θmatch=cMatch*ε)
    (hmatch:cMatch≤min (s.ζhub*s.γ*(1/4:ℝ)) (s.ζlocal*(1/4:ℝ))/2):
    s.hpack≤(2*h-ζparent)-ξreserve-ζout ∧
    θmatch≤(min (s.ζhub*s.γ*(1/4:ℝ)) (s.ζlocal*(1/4:ℝ))/2)*ε :=by
  constructor
  · rw [hsPack]
    exact ordinary_parent_root_packing_slack h ζparent geomCap ξreserve ζout hζ hgeom hξ hout
  · rw [hθ]
    exact mul_le_mul_of_nonneg_right hmatch hε
end Oberwolfach
