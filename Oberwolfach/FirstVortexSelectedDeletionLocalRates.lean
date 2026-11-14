module

public import Oberwolfach.FirstVortexSelectedSeedLocalRates
public import Oberwolfach.FirstVortexEarlyDeletionRateBound

@[expose] public section
/-! Use the selector's chosen early deletion rate and exact seed formulas
in the same local bounds, without choosing replacement parameters. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_selected_deletion_local_rates
    (d K:ℕ) (cap rho tLocal eta δsmall δspoke s θ lam eps ζOrd:ℝ)
    (hd:0<d) (hK:1≤K) (hs:0<s) (hθ:0<θ) (hθ1:θ≤1) (hlam:0<lam) (heps:0<eps)
    (hθs:θ≤s) (hlams:lam≤s)
    (hepsRate:3*eps≤lam*(θ/(100*(K:ℝ)^2))) (hζOrd:ζOrd≤eps/8)
    (hlocal:∀ζret ηBalance θ' a γ ξPart κ Δ b:ℝ,
      ζret≤s→ηBalance≤s→θ'≤s→a≤s→γ≤s→ξPart≤s→κ≤s→Δ≤s→b≤s→
      FirstVortexLocalGeometryRateBounds cap rho tLocal eta δsmall δspoke ζret ηBalance θ' a γ ξPart κ Δ b)
    (ζret ηBalance ξPart κ b:ℝ)
    (hζ:ζret≤s) (hbal:ηBalance≤s) (hξ:ξPart≤s) (hκ:κ≤s) (hb:b≤s):
    let a:=min (lam/(10*(d:ℝ))) (θ/(200*(K:ℝ)^2))
    let γ:=min (eps/2) (min (1/2:ℝ) (min (lam/(10*(d:ℝ))) (lam/10)));
    ζOrd≤s ∧ 0<a ∧ 0<γ ∧
      FirstVortexLocalGeometryRateBounds cap rho tLocal eta δsmall δspoke ζret ηBalance θ a γ ξPart κ ζOrd b :=by
  intro a γ
  have hdel:=first_vortex_early_deletion_rate_bound lam θ eps ζOrd K hlam.le hθ1 hK hepsRate hζOrd
  have hdelS:ζOrd≤s:=by linarith
  have hh:=first_vortex_selected_seed_local_rates d K cap rho tLocal eta δsmall δspoke s θ lam eps
    hd (by omega) hs hθ hlam heps hθs hlams hlocal ζret ηBalance ξPart κ ζOrd b hζ hbal hξ hκ hdelS hb
  exact ⟨hdelS,hh⟩
end Oberwolfach
