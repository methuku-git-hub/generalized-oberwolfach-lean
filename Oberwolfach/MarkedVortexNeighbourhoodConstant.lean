module

public import Oberwolfach.AsymptoticMargins

@[expose] public section
/-! A single positive level constant handles both inner vertex and hub sizes. -/
set_option autoImplicit false
namespace Oberwolfach

theorem marked_vortex_neighbourhood_constant_exists
    (ε ρ₀:ℝ) (he:0<ε) (hρ:0<ρ₀):
    ∃K:ℝ,1≤K ∧ 1≤K*(ε/2) ∧ 1≤K*(ρ₀/8)*(ε/2) := by
  let K:=max 1 (max (2/ε) (16/(ρ₀*ε)))
  have hK1:1≤K:=le_max_left _ _
  have hKI:2/ε≤K:=(le_max_left _ _).trans (le_max_right _ _)
  have hKJ:16/(ρ₀*ε)≤K:=(le_max_right _ _).trans (le_max_right _ _)
  have hscaleI:=mul_le_mul_of_nonneg_right hKI (show 0≤ε/2 by positivity)
  have hscaleJ:=mul_le_mul_of_nonneg_right hKJ (show 0≤(ρ₀/8)*(ε/2) by positivity)
  have hEI:(2/ε)*(ε/2)=1:=by field_simp
  have hEJ:(16/(ρ₀*ε))*((ρ₀/8)*(ε/2))=1:=by field_simp; norm_num
  refine ⟨K,hK1,?_,?_⟩
  · linarith
  · nlinarith
end Oberwolfach
