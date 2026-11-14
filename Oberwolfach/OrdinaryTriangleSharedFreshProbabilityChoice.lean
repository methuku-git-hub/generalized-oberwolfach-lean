module

public import Mathlib.Tactic

@[expose] public section
/-! Resolve the choice order when geometry supplies a probability cap before
packing supplies η and the fresh sampler chooses the actual probability. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_shared_fresh_probability_choice
    (pGeo pcap:ℝ) (hpGeo:0<pGeo) (hpcap:0<pcap)
    (Geometry:ℝ→ℝ→ℝ→ℝ→Prop) (Certificate:ℝ→ℝ→ℝ→Prop)
    (hGeometry:∀η:ℝ,0<η→∃eps γ:ℝ,0<eps ∧ 0<γ ∧
      ∀p:ℝ,0≤p→p≤pGeo→Geometry η p eps γ)
    (hCertificate:∀pbound:ℝ,0<pbound→∃p:ℝ,0<p ∧ p≤pbound ∧
      ∃η:ℝ,0<η ∧ ∀eps:ℝ,0<eps→Certificate p η eps):
    ∃p η eps γ:ℝ,0<p ∧ p≤pGeo ∧ p≤pcap ∧ 0<η ∧ 0<eps ∧ 0<γ ∧
      Geometry η p eps γ ∧ Certificate p η eps :=by
  obtain ⟨p,hp,hpbound,η,hη,hcert⟩:=hCertificate (min pGeo pcap) (lt_min hpGeo hpcap)
  have hpGeo':p≤pGeo:=hpbound.trans (min_le_left _ _)
  have hpcap':p≤pcap:=hpbound.trans (min_le_right _ _)
  obtain ⟨eps,γ,heps,hγ,hgeo⟩:=hGeometry η hη
  exact ⟨p,η,eps,γ,hp,hpGeo',hpcap',hη,heps,hγ,hgeo p hp.le hpGeo',hcert eps heps⟩
end Oberwolfach
