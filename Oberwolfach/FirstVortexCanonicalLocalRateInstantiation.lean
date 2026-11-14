module

public import Oberwolfach.FirstVortexLateCanonicalRates

@[expose] public section
/-! Insert the selector's actual seed parameter formulas into the common
local-rate bound, retaining arbitrary later rates within the chosen cap. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_canonical_local_rate_instantiation
    (d K:ℕ) (cap rho tLocal eta δsmall δspoke s θ lam:ℝ)
    (hd:0<d) (hK:0<K) (hs:0<s) (hθ:0<θ) (hlam:0<lam) (hθs:θ≤s) (hlams:lam≤s)
    (hlocal:∀ζret ηBalance θ' a γ ξPart κ Δ b:ℝ,
      ζret≤s→ηBalance≤s→θ'≤s→a≤s→γ≤s→ξPart≤s→κ≤s→Δ≤s→b≤s→
      FirstVortexLocalGeometryRateBounds cap rho tLocal eta δsmall δspoke ζret ηBalance θ' a γ ξPart κ Δ b)
    (ζret ηBalance ξPart κ Δ b:ℝ)
    (hζ:ζret≤s) (hbal:ηBalance≤s) (hξ:ξPart≤s) (hκ:κ≤s) (hΔ:Δ≤s) (hb:b≤s):
    ∃eps a γ:ℝ,0<eps ∧ eps≤1 ∧ 3*eps≤lam*(θ/(100*(K:ℝ)^2)) ∧
      a=min (lam/(10*(d:ℝ))) (θ/(200*(K:ℝ)^2)) ∧
      γ=min (eps/2) (min (1/2:ℝ) (min (lam/(10*(d:ℝ))) (lam/10))) ∧
      0<a ∧ 0<γ ∧
      FirstVortexLocalGeometryRateBounds cap rho tLocal eta δsmall δspoke ζret ηBalance θ a γ ξPart κ Δ b :=by
  obtain ⟨eps,a,γ,heps,heps1,hepsrate,haeq,hγeq,ha,hγ,has,hγs⟩:=
    first_vortex_late_canonical_rates d K lam θ s hd hK hlam hθ hs hlams
  exact ⟨eps,a,γ,heps,heps1,hepsrate,haeq,hγeq,ha,hγ,
    hlocal ζret ηBalance θ a γ ξPart κ Δ b hζ hbal hθs has hγs hξ hκ hΔ hb⟩
end Oberwolfach
