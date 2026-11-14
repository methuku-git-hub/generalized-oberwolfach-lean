module

public import Oberwolfach.OrdinaryVortexTriangleRootGeometryAtScale
public import Oberwolfach.OrdinaryVortexTriangleRootCoverStaticGeometryOrdered

@[expose] public section
/-! Choose the reserve probability before the packing-balance tolerance and
then provide the actual vortex root-cover geometry at that tolerance. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_triangle_root_geometry_ordered_named
    (r k:ℕ) (ρ₀ βparent b B εparent gap cap:ℝ)
    (hk:4≤k) (hρ₀:0<ρ₀) (hβ:0<βparent) (hb:0<b) (hB:0≤B)
    (hgap:0<gap) (hcap:0<cap):
    ∃βout ξ ζ:ℝ,0<βout ∧ βout=βparent/2 ∧ 0<ξ ∧ 0<ζ ∧ ξ≤cap ∧ ζ≤cap ∧
    ∀pcap:ℝ,0<pcap→∃p:ℝ,0<p ∧ p≤1 ∧ p≤pcap ∧
    ∀η:ℝ,0<η→∃eps γ:ℝ,0<eps ∧ eps≤1 ∧ 0<γ ∧
      OrdinaryVortexTriangleRootGeometryAtScale r k ρ₀ βparent b B εparent gap η βout ξ ζ p eps γ :=by
  obtain ⟨βout,ξ,ζ,hβout,hβeq,hξ,hζ,hcapξ,hcapζ,hmain⟩:=
    ordinary_vortex_triangle_root_cover_static_geometry_ordered r k ρ₀ βparent b B εparent gap cap
      hk hρ₀ hβ hb hB hgap hcap
  refine ⟨βout,ξ,ζ,hβout,hβeq,hξ,hζ,hcapξ,hcapζ,?_⟩
  intro pcap hpcap
  obtain ⟨p,hp,hp1,hpc,hmain⟩:=hmain pcap hpcap
  refine ⟨p,hp,hp1,hpc,?_⟩
  intro η hη
  obtain ⟨eps,γ,heps,heps1,hγ,hmain⟩:=hmain η hη
  exact ⟨eps,γ,heps,heps1,hγ,hmain⟩
end Oberwolfach
