module

public import Oberwolfach.MarkedDeepRatioParameterChoice

@[expose] public section
/-! With a fixed geometric constant, choose the vortex ratio below an
arbitrary positive cap before selecting the active density and deep error. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_fixed_geometry_deep_ratio_choice
    (r:ℕ) (ρ ρ₀ t κ ξcap K εcap:ℝ)
    (hρ:0<ρ) (hρ₀:0<ρ₀) (ht:0<t) (hκ:0<κ) (hξ:0<ξcap) (hK:0≤K) (hcap:0<εcap):
    ∃ ε₀:ℝ,0<ε₀ ∧ ε₀≤εcap ∧ ∀ ε:ℝ,0<ε→ε≤ε₀→
      ∃ ω ξ:ℝ,0<ω ∧ ω≤1 ∧ 0<ξ ∧ ω≤ε/8 ∧ ω≤ρ₀*ε/64 ∧ ε^2≤ξ ∧ ξ≤ξcap ∧
        (4*K+(3*r+50:ℕ))*ξ≤κ/2 ∧ (1+2/ρ)*ξ≤t*ω/32:=by
  obtain ⟨base,hbase,hchoose⟩:=marked_deep_ratio_parameter_choice r ρ ρ₀ t κ ξcap K hρ hρ₀ ht hκ hξ hK
  let ε₀:=min base (min εcap 1)
  have hε₀:0<ε₀:=by dsimp [ε₀];positivity
  have hεcap:ε₀≤εcap:=(min_le_right _ _).trans (min_le_left _ _)
  refine ⟨ε₀,hε₀,hεcap,?_⟩
  intro ε he he₀
  have hebase:ε≤base:=he₀.trans (min_le_left _ _)
  have he1:ε≤1:=he₀.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hKC:K≤K/ε:=by
    apply (le_div_iff₀ he).2
    nlinarith [mul_nonneg hK (sub_nonneg.mpr he1)]
  obtain ⟨ω,ξ,hω,hξ',hωv,hωu,hxi,hxicap,hscale,hgap⟩:=hchoose ε he hebase K hK hKC
  have hω1:ω≤1:=by linarith
  exact ⟨ω,ξ,hω,hω1,hξ',hωv,hωu,hxi,hxicap,hscale,hgap⟩
end Oberwolfach
