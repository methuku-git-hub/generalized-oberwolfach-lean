module

public import Oberwolfach.OrdinaryPairingFixedMarginChoicesExplicit
public import Oberwolfach.OrdinaryVortexDomainMarginLinear

@[expose] public section
/-! The pairing and cleanup margins can be chosen with explicit lower
    bounds proportional to the fixed vortex shrinkage parameter. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_pairing_margins_linear
    (m:ℕ) (hm:3≤m) (p₀ gap ρ₀ b B:ℝ)
    (hp:0<p₀) (hp1:p₀≤1) (hgap:0<gap) (hρ:0<ρ₀) (hb:0<b) (hB:0≤B):
    ∃ce ch:ℝ,0<ce ∧ 0<ch ∧ ∀ε:ℝ,0<ε→ε≤1→
    let K:ℝ:=2*(1+1/(ε/2)+1/((ε/2)*(ρ₀/8)))
    let βe:=p₀^3*gap/(4*K);let βh:=p₀^2*(ρ₀/8)/(4*K);
    ce*ε≤βe ∧ ch*ε≤βh ∧
    ∃γ κ a εf ηf ζ:ℝ,0<βe ∧ 0<βh ∧ 0<γ ∧ 0<κ ∧ γ≤βe ∧ κ≤βe ∧ 0<a ∧ a≤1 ∧
      0<εf ∧ 0<ηf ∧ 0<ζ ∧
      OrdinaryCleanupFixedMarginsProperty p₀ gap (ρ₀/8) K βe βh ∧
      OrdinaryGeneralFreshPairingProbabilityProperty m γ κ b B p₀ a εf ηf ζ ∧
    ∀cap:ℝ,0<cap→∃lam:ℝ,0<lam ∧ lam≤cap ∧
      lam≤(p₀^3*gap)/12 ∧ lam≤(p₀^2*(ρ₀/8))/8 ∧
      a*K+2*lam≤p₀/2 ∧ a*K+2*lam≤p₀*(ρ₀/8) ∧ 6*lam≤ηf*a :=by
  let ce:ℝ:=p₀^3*gap/(4*(6+32/ρ₀))
  let ch:ℝ:=p₀^2*(ρ₀/8)/(4*(6+32/ρ₀))
  have hce:0<ce:=by dsimp [ce];positivity
  have hch:0<ch:=by dsimp [ch];positivity
  refine ⟨ce,ch,hce,hch,?_⟩
  intro ε hε hε1 K βe βh
  have he:=ordinary_vortex_domain_margin_linear ε ρ₀ (p₀^3*gap) hε hε1 hρ (by positivity)
  have hh:=ordinary_vortex_domain_margin_linear ε ρ₀ (p₀^2*(ρ₀/8)) hε hε1 hρ (by positivity)
  have hK:0<K:=he.1
  refine ⟨he.2.2,hh.2.2,?_⟩
  exact ordinary_pairing_fixed_margin_choices_explicit m hm p₀ gap (ρ₀/8) K b B hp hp1 hgap (by positivity) hK hb hB
end Oberwolfach
