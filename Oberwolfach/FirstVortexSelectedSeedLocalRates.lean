module

public import Oberwolfach.FirstVortexCanonicalLocalRateInstantiation

@[expose] public section
/-! The selector chooses its own positive error parameter. Its exact seed
formulas satisfy the local rate bounds for every such chosen parameter. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_selected_seed_local_rates
    (d K:ℕ) (cap rho tLocal eta δsmall δspoke s θ lam eps:ℝ)
    (hd:0<d) (hK:0<K) (hs:0<s) (hθ:0<θ) (hlam:0<lam) (heps:0<eps)
    (hθs:θ≤s) (hlams:lam≤s)
    (hlocal:∀ζret ηBalance θ' a γ ξPart κ Δ b:ℝ,
      ζret≤s→ηBalance≤s→θ'≤s→a≤s→γ≤s→ξPart≤s→κ≤s→Δ≤s→b≤s→
      FirstVortexLocalGeometryRateBounds cap rho tLocal eta δsmall δspoke ζret ηBalance θ' a γ ξPart κ Δ b)
    (ζret ηBalance ξPart κ Δ b:ℝ)
    (hζ:ζret≤s) (hbal:ηBalance≤s) (hξ:ξPart≤s) (hκ:κ≤s) (hΔ:Δ≤s) (hb:b≤s):
    let a:=min (lam/(10*(d:ℝ))) (θ/(200*(K:ℝ)^2))
    let γ:=min (eps/2) (min (1/2:ℝ) (min (lam/(10*(d:ℝ))) (lam/10)));
    0<a ∧ 0<γ ∧
      FirstVortexLocalGeometryRateBounds cap rho tLocal eta δsmall δspoke ζret ηBalance θ a γ ξPart κ Δ b :=by
  intro a γ
  have hdR:(1:ℝ)≤d:=by exact_mod_cast hd
  have hKR:(0:ℝ)<K:=by exact_mod_cast hK
  have ha:0<a:=by dsimp [a];positivity
  have hγ:0<γ:=by dsimp [γ];positivity
  have hdiv:lam/(10*(d:ℝ))≤lam:=by
    apply (div_le_iff₀ (show 0<10*(d:ℝ) by positivity)).2
    nlinarith
  have has:a≤s:=(min_le_left _ _).trans (hdiv.trans hlams)
  have hγs:γ≤s:=by
    have hh:γ≤lam/(10*(d:ℝ)):=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    exact hh.trans (hdiv.trans hlams)
  exact ⟨ha,hγ,hlocal ζret ηBalance θ a γ ξPart κ Δ b hζ hbal hθs has hγs hξ hκ hΔ hb⟩
end Oberwolfach
