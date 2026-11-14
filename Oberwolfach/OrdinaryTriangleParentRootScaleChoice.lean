module

public import Oberwolfach.OrdinaryTriangleParentEditScaleChoice
public import Oberwolfach.OrdinaryUniformRootReferenceAtScale

@[expose] public section
/-! Select the triangle parent edit rate and the nonroot reference scale in
an order compatible with the common cut event and with an arbitrary host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryTriangleEditScaleAt
    (βH ηH B ω pstar βparent εparent ζ rate:ℝ) (N₀:ℕ):Prop :=
  βparent+ζ≤βH ∧
  ∀N U L:ℝ,(N₀:ℝ)≤N→ω*N≤U→0≤L→L≤rate*N→
    L≤ζ*N ∧ L≤ζ*U ∧
    8*(L+1)≤(βH-βparent)*N ∧
    5*(3:ℝ)^4*(L+1)≤(βH-βparent)*N ∧
    ηH+8*(3:ℝ)^4*(B/(ω*pstar^(2*3-1)))*L/N≤εparent

theorem ordinary_triangle_parent_root_scale_choice
    (k:ℕ) (hk:4≤k) (α βH ηH c B ω pstar δ h gap:ℝ)
    (hβH:0<βH) (hηH:0<ηH) (hc:0≤c) (hB:0≤B) (hω:0<ω) (hp:0<pstar)
    (hδ:0<δ) (hδ1:δ<1) (hh:0<h) (hgap:0<gap):
    ∃βparent εparent ζ rate lam:ℝ,0<βparent ∧ 0<εparent ∧ 0<ζ ∧ 0<rate ∧ 0<lam ∧ ζ≤h ∧
    ∃N₀:ℕ,1≤N₀ ∧
    OrdinaryTriangleEditScaleAt βH ηH B ω pstar βparent εparent ζ rate N₀ ∧
    OrdinaryUniformRootReferenceAtScale 3 (by omega) k α βparent c (B/(ω*pstar^(2*3-1)))
      (2*h-ζ) δ εparent ω gap lam :=by
  obtain ⟨βparent,εparent,ζ,rate,hβparent,hεparent,hζ,hrate,hζcap,hdegree,N₀,hN₀,hscales⟩:=
    ordinary_triangle_parent_edit_scale_choice βH ηH B ω pstar h hβH hηH hB hω hp hh
  have hBseed:0≤B/(ω*pstar^(2*3-1)):=by positivity
  have hcut:0≤2*h-ζ:=by linarith
  obtain ⟨lam,hlam,hroot⟩:=ordinary_root_reference_from_global_parent_uniform 3 (by omega) k hk α βparent c
    (B/(ω*pstar^(2*3-1))) (2*h-ζ) δ εparent ω gap
    hβparent hδ hδ1 hω hgap hBseed hc hcut
  refine ⟨βparent,εparent,ζ,rate,lam,hβparent,hεparent,hζ,hrate,hlam,hζcap,N₀,hN₀,?_,?_⟩
  · exact ⟨hdegree,hscales⟩
  · exact hroot
end Oberwolfach
