module

public import Oberwolfach.OrdinaryUnreservedPackingMargins

@[expose] public section
/-! Choose the edit and reserve losses after the source constants and
packing tolerance, while fixing the final cut and degree constants first. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach

theorem ordinary_two_stage_packing_margin_choice (r:ℕ) (βsource h B εstar:ℝ)
    (hβ:0<βsource) (hh:0<h) (hB:0≤B) (hε:0<εstar):
    ∃tedit treserve:ℝ,0<tedit ∧ 0<treserve ∧
    ∀a ζedit ξ ζreserve:ℝ,
      0≤a→0≤ζedit→0≤ξ→0≤ζreserve→
      a≤tedit→ζedit≤tedit→ξ≤treserve→ζreserve≤treserve→
      h/4≤(h-ζedit)-ξ-ζreserve ∧
      βsource/2+ζedit≤βsource ∧
      8*a≤βsource-βsource/2 ∧
      5*(r:ℝ)^4*a≤βsource-βsource/2 ∧
      εstar/4+8*(r:ℝ)^4*B*a≤εstar/2 ∧
      βsource/4+ξ+ζreserve≤βsource/2 ∧
      8*(ξ+ζreserve)≤βsource/2-βsource/4 ∧
      5*(r:ℝ)^4*(ξ+ζreserve)≤βsource/2-βsource/4 ∧
      εstar/2+8*(r:ℝ)^4*B*(ξ+ζreserve)≤εstar:=by
  obtain ⟨te,hte,hevent⟩:=ordinary_unreserved_packing_margin_choice r βsource h B (εstar/4) (εstar/2)
    hβ hh hB (by linarith)
  obtain ⟨tr,htr,hr⟩:=ordinary_unreserved_packing_margin_choice r (βsource/2) (h/2) B (εstar/2) εstar
    (by positivity) (by positivity) hB (by linarith)
  refine ⟨te,tr,hte,htr,?_⟩
  intro a ζedit ξ ζreserve ha hz hx hzr hat hzt hxt hzrt
  have he:=hevent a 0 ha (by norm_num) hat hte.le
  have hc:=hevent ζedit 0 hz (by norm_num) hzt hte.le
  have hres:=hr ξ ζreserve hx hzr hxt hzrt
  rcases he with ⟨_,_,heI,heT,heW⟩
  rcases hc with ⟨hcCut,hcDeg,_,_,_⟩
  rcases hres with ⟨hrCut,hrDeg,hrI,hrT,hrW⟩
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;>
    nlinarith only [hcCut,hcDeg,heI,heT,heW,hrCut,hrDeg,hrI,hrT,hrW]
end Oberwolfach
