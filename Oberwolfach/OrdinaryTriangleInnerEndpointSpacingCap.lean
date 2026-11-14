module

public import Oberwolfach.OrdinaryTriangleInnerEndpointPreselect

@[expose] public section
/-! The vortex spacing can be chosen below the hub tolerance before the
failure allowance and the graph are supplied. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_inner_endpoint_spacing_cap
    (α ξ ηHub:ℝ) (hα:0<α) (hξ:0≤ξ) (hgap:ξ<ηHub):
    ∃βcap:ℝ,0<βcap ∧ ∀β:ℝ,0≤β→β≤βcap→
      β≤1/4 ∧ β≤α/8 ∧ ξ+2*β<ηHub :=by
  let βcap:ℝ:=min (1/8) (min (α/16) ((ηHub-ξ)/4))/2
  have hdiff:0<ηHub-ξ:=sub_pos.mpr hgap
  have hp:0<βcap:=by dsimp [βcap];positivity
  have h1:βcap≤1/16:=by have hh:=min_le_left (1/8:ℝ) (min (α/16) ((ηHub-ξ)/4));dsimp [βcap];linarith
  have h2:βcap≤α/32:=by have hh: min (1/8:ℝ) (min (α/16) ((ηHub-ξ)/4))≤α/16:=
      (min_le_right _ _).trans (min_le_left _ _);dsimp [βcap];linarith
  have h3:βcap≤(ηHub-ξ)/8:=by have hh: min (1/8:ℝ) (min (α/16) ((ηHub-ξ)/4))≤(ηHub-ξ)/4:=
      (min_le_right _ _).trans (min_le_right _ _);dsimp [βcap];linarith
  refine ⟨βcap,hp,?_⟩
  intro β _ hβ
  refine ⟨by linarith,by linarith,?_⟩
  linarith
end Oberwolfach
