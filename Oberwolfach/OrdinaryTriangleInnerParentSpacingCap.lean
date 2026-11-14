module

public import Oberwolfach.OrdinaryTriangleInnerEndpointSpacingCap

@[expose] public section
/-! One positive vortex spacing cap satisfies both the inner-hub event and
the exact deep-parent balance before the later failure allowance. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_inner_parent_spacing_cap
    (α ξ ηHub δ κe pmin othercap:ℝ)
    (hα:0<α) (hξ:0≤ξ) (hgap:ξ<ηHub) (hδ:0<δ) (hκe:0<κe) (hpmin:0<pmin) (hother:0<othercap):
    ∃βcap:ℝ,0<βcap ∧ βcap≤othercap ∧ ∀β:ℝ,0≤β→β≤βcap→
      β≤1/4 ∧ β≤α/8 ∧ ξ+2*β<ηHub ∧ β≤2*δ*κe*pmin :=by
  obtain ⟨cap0,hcap0,hsetup⟩:=ordinary_triangle_inner_endpoint_spacing_cap α ξ ηHub hα hξ hgap
  let βcap:ℝ:=min cap0 (min (δ*κe*pmin) othercap)/2
  have hp:0<βcap:=by dsimp [βcap];positivity
  have hcap:βcap≤cap0:=by have hh:=min_le_left cap0 (min (δ*κe*pmin) othercap);dsimp [βcap];linarith
  have hother':βcap≤othercap:=by
    have hh: min cap0 (min (δ*κe*pmin) othercap)≤othercap:=
      (min_le_right _ _).trans (min_le_right _ _)
    dsimp [βcap];linarith
  have hbalance:βcap≤δ*κe*pmin:=by
    have hh: min cap0 (min (δ*κe*pmin) othercap)≤δ*κe*pmin:=
      (min_le_right _ _).trans (min_le_left _ _)
    have hprod:0≤δ*κe*pmin:=by positivity
    dsimp [βcap];linarith
  refine ⟨βcap,hp,hother',?_⟩
  intro β hβ hβcap
  obtain ⟨h1,h2,h3⟩:=hsetup β hβ (hβcap.trans hcap)
  have hprod:0≤δ*κe*pmin:=by positivity
  exact ⟨h1,h2,h3,by linarith⟩
end Oberwolfach
