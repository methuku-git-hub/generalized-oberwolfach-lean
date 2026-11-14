module

public import Oberwolfach.OrdinaryCleanupFixedMarginsProperty
public import Oberwolfach.OrdinaryPairingFreshOrderedChoices

@[expose] public section
/-! Fix positive cleanup margins and the pairing parent scales before
    choosing an arbitrarily small later edit tolerance. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_pairing_fixed_margin_choices
    (m:ℕ) (hm:3≤m) (p₀ gap κinner K b B:ℝ)
    (hp:0<p₀) (hp1:p₀≤1) (hgap:0<gap) (hκinner:0<κinner) (hK:0<K)
    (hb:0<b) (hB:0≤B):
    ∃βe βh γ κ a εf ηf ζ:ℝ,
      0<βe ∧ 0<βh ∧ 0<γ ∧ 0<κ ∧ γ≤βe ∧ κ≤βe ∧ 0<a ∧ a≤1 ∧
      0<εf ∧ 0<ηf ∧ 0<ζ ∧
      OrdinaryCleanupFixedMarginsProperty p₀ gap κinner K βe βh ∧
      OrdinaryGeneralFreshPairingProbabilityProperty m γ κ b B p₀ a εf ηf ζ ∧
    ∀cap:ℝ,0<cap→∃lam:ℝ,0<lam ∧ lam≤cap ∧
      lam≤(p₀^3*gap)/12 ∧ lam≤(p₀^2*κinner)/8 ∧
      a*K+2*lam≤p₀/2 ∧ a*K+2*lam≤p₀*κinner ∧ 6*lam≤ηf*a :=by
  obtain ⟨βe,βh,hβe,hβh,hfixed⟩:=ordinary_cleanup_fixed_margins_property p₀ gap κinner K hp hgap hκinner hK
  let γ:=βe/2
  let κ:=βe/2
  have hγ:0<γ:=by dsimp [γ];positivity
  have hκ:0<κ:=by dsimp [κ];positivity
  obtain ⟨a,εf,ηf,ζ,ha,ha1,hεf,hηf,hζ,hprob,hordered⟩:=
    ordinary_pairing_fresh_ordered_choices m hm γ κ b B p₀ κinner K hγ hκ hb hB hp hp1 hκinner hK
  refine ⟨βe,βh,γ,κ,a,εf,ηf,ζ,hβe,hβh,hγ,hκ,by dsimp [γ];linarith,by dsimp [κ];linarith,
    ha,ha1,hεf,hηf,hζ,hfixed,hprob,?_⟩
  intro cap hcap
  let cap':=min cap (min ((p₀^3*gap)/12) ((p₀^2*κinner)/8))
  have hc:0<cap':=by dsimp [cap'];positivity
  obtain ⟨lam,hlam,hlamcap,hR,hH,herr⟩:=hordered cap' hc
  exact ⟨lam,hlam,hlamcap.trans (min_le_left _ _),
    hlamcap.trans ((min_le_right _ _).trans (min_le_left _ _)),
    hlamcap.trans ((min_le_right _ _).trans (min_le_right _ _)),hR,hH,herr⟩
end Oberwolfach
