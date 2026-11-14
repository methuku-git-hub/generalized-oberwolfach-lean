module

public import Oberwolfach.OrdinaryTriangleSeparatedNumericScales

@[expose] public section
/-! Permit any earlier positive cap on both numerical scales. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_separated_numeric_scales_capped
    (p γ ω θ ρ ρhub η cap:ℝ)
    (hp:0<p) (hγ:0<γ) (hω:0<ω) (hθ:0<θ) (hρ:0<ρ) (hρhub:0<ρhub) (hη:0<η) (hcap:0<cap):
    ∃b a₀:ℝ,0<b ∧ b≤cap ∧ 0<a₀ ∧ a₀≤cap ∧
      6*b≤p^6*γ/4 ∧ 6*b≤(p^6*γ/4)*ω ∧ b≤p^6*γ/8 ∧ b≤(p^6*γ/8)*ω ∧ b≤θ ∧
      2*b≤ω*p*η ∧
      ∀a:ℝ,0≤a→a≤a₀→b+12*a≤ρhub ∧ 3*b+24*a≤ρ/2 :=by
  obtain ⟨b₀,a₁,hb,ha,h1,h2,h3,h4,h5,h6,hbudget⟩:=
    ordinary_triangle_separated_numeric_scales p γ ω θ ρ ρhub η hp hγ hω hθ hρ hρhub hη
  let b:=min b₀ cap
  let a₀:=min a₁ cap
  have hbpos:0<b:=lt_min hb hcap
  have hapos:0<a₀:=lt_min ha hcap
  have hb0:b≤b₀:=min_le_left _ _
  have ha0:a₀≤a₁:=min_le_left _ _
  refine ⟨b,a₀,hbpos,min_le_right _ _,hapos,min_le_right _ _,?_,?_,?_,?_,?_,?_,?_⟩
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · intro a ha' haa
    have hh:=hbudget a ha' (haa.trans ha0)
    constructor <;> linarith [hh.1,hh.2]
end Oberwolfach
