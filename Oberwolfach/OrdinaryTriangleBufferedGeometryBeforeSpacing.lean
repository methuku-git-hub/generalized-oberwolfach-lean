module

public import Oberwolfach.OrdinaryVortexBufferedRootStaticGeometrySeparateAtScale

@[expose] public section
/-! The triangle sharp-cover geometry and its reserve scales can be chosen
before the later conflict size, while retaining the selected parent margins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_buffered_geometry_before_spacing
    (k:ℕ) (ρ₀ βH cParent Bparent pstar δ href εstar ηH gapRoot:ℝ)
    (hk:4≤k) (hρ₀:0<ρ₀) (hβH:0<βH) (hc:0<cParent) (hB:0≤Bparent) (hpstar:0<pstar)
    (hδ:0<δ) (hδsmall:δ<1/8) (hhref:0<href) (hηH:0<ηH) (hgapRoot:0<gapRoot)
    (hfit:2*ηH+gapRoot<εstar):
    let bRoot:=cParent*(1-2*δ)^2
    let BRoot:=Bparent/((ρ₀/16)*pstar^(2*3-1))
    let gapGeo:=εstar-(2*ηH+gapRoot);
    ∃ξ ζ edit:ℝ,0<ξ ∧ 0<ζ ∧ 0<edit ∧ ξ≤href/4 ∧ ζ≤href/4 ∧ ξ+ζ≤href/2 ∧
    (∀ζroot:ℝ,ζroot≤href→href/4≤(2*href-ζroot)-ξ-ζ) ∧
    ∀pcap:ℝ,0<pcap→∃p:ℝ,0<p ∧ p≤1 ∧ p≤pcap ∧
    ∀η:ℝ,0<η→∃eps γ:ℝ,0<eps ∧ eps≤1 ∧ 0<γ ∧
      OrdinaryVortexBufferedRootStaticGeometrySeparateAtScale 3 k 2 ρ₀ (βH/4) bRoot BRoot
        (2*ηH+gapRoot) gapGeo (βH/8) ξ ζ edit p η eps γ :=by
  intro bRoot BRoot gapGeo
  have hbase:0<1-2*δ:=by linarith
  have hb:0<bRoot:=by dsimp [bRoot];positivity
  have hB':0≤BRoot:=by dsimp [BRoot];positivity
  have hgap:0<gapGeo:=by dsimp [gapGeo];linarith
  obtain ⟨βout,ξ,ζ,edit,hβout,hβeq,hξ,hζ,hedit,hξcap,hζcap,hgeometry⟩:=
    ordinary_vortex_buffered_root_static_geometry_separate_at_scale_choice 3 k 2 (by omega)
      ρ₀ (βH/4) bRoot BRoot (2*ηH+gapRoot) gapGeo (href/4)
      hk hρ₀ (by positivity) hb hB' hgap (by positivity)
  have hβeq':βout=βH/8:=by linarith
  subst βout
  have heq:βH/4/2=βH/8:=by ring
  rw [heq] at hgeometry
  refine ⟨ξ,ζ,edit,hξ,hζ,hedit,hξcap,hζcap,by linarith,?_,hgeometry⟩
  intro ζroot hζroot
  linarith
end Oberwolfach
