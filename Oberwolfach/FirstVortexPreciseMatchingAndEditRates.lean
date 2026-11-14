module

public import Oberwolfach.FirstVortexPreciseMatchingRateChoice

@[expose] public section
/-! Keep a strict gap between the matching error and the later class edit,
so the actual edge count and precise degree estimates hold together. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_precise_matching_and_edit_rates
    (a cap θ ε upper:ℝ) (ha:0<a) (hcap:0<cap) (hθ:0<θ) (hε:0<ε) (hupper:0<upper):
    ∃lamBase lamAssign ξCap:ℝ,
      0<lamBase ∧ 0<lamAssign ∧ lamBase≤lamAssign ∧ lamAssign≤upper ∧
      lamAssign≤1 ∧ lamAssign≤θ ∧ lamAssign≤cap*a/4096 ∧ 0<ξCap ∧
      ∀ξ:ℝ,ξ≤ξCap→lamBase+ξ≤a*θ/4096 ∧ ξ/2≤(lamAssign-lamBase)*ε :=by
  obtain ⟨lam,ξ₀,hlam,hupper',h1,hθ',hcap',hξ₀,hsmall⟩:=first_vortex_precise_matching_rate_choice a cap θ upper ha hcap hθ hupper
  let lamBase:ℝ:=lam/2
  let ξCap:ℝ:=min ξ₀ (lam*ε)
  have hbase:0<lamBase:=by dsimp [lamBase];positivity
  have hbasele:lamBase≤lam:=by dsimp [lamBase];linarith
  have hξ:0<ξCap:=by dsimp [ξCap];positivity
  refine ⟨lamBase,lam,ξCap,hbase,hlam,hbasele,hupper',h1,hθ',hcap',hξ,?_⟩
  intro ξ hξCap
  have hξ₀':ξ≤ξ₀:=hξCap.trans (min_le_left _ _)
  have hξε:ξ≤lam*ε:=hξCap.trans (min_le_right _ _)
  have hh:=hsmall ξ hξ₀'
  constructor
  · linarith
  · dsimp only [lamBase]
    nlinarith only [hξε]
end Oberwolfach
