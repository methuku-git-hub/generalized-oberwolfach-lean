module

public import Oberwolfach.FirstVortexSelectedDeletionLocalRates
public import Oberwolfach.FirstVortexSeparateEtaCoarseGlobalRates

@[expose] public section
/-! The selector's actual seed and deletion rates meet both the local
outside-change and global matching-loss margins with separate errors. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_selected_deletion_split_eta_rates
    (d K:ℕ) (globalCap rho tLocal etaLocal etaGlobal δsmall δspoke s θ lam eps ζOrd:ℝ)
    (hd:0<d) (hK:1≤K) (hcap:0≤globalCap) (hrho:0<rho) (hs:0<s)
    (hηLocal:0≤etaLocal) (hθ:0<θ) (hθ1:θ≤1) (hlam:0<lam) (heps:0<eps)
    (hθs:θ≤s) (hlams:lam≤s)
    (hroom:2*(1+2/rho)*etaGlobal≤globalCap/2)
    (hepsRate:3*eps≤lam*(θ/(100*(K:ℝ)^2))) (hζOrd:ζOrd≤eps/8)
    (hlocal:∀ζret ηBalance θ' a γ ξPart κ Δ b:ℝ,
      ζret≤s→ηBalance≤s→θ'≤s→a≤s→γ≤s→ξPart≤s→κ≤s→Δ≤s→b≤s→
      FirstVortexLocalGeometryRateBounds (globalCap/2) rho tLocal etaLocal δsmall δspoke ζret ηBalance θ' a γ ξPart κ Δ b)
    (ζret ηBalance ξPart κ b:ℝ)
    (hζ:ζret≤s) (hbal:ηBalance≤s) (hξ:ξPart≤s) (hκ:κ≤s) (hb:b≤s):
    let a:=min (lam/(10*(d:ℝ))) (θ/(200*(K:ℝ)^2))
    let γ:=min (eps/2) (min (1/2:ℝ) (min (lam/(10*(d:ℝ))) (lam/10)));
    ζOrd≤s ∧ 0<a ∧ 0<γ ∧
    FirstVortexLocalGeometryRateBounds (globalCap/2) rho tLocal etaLocal δsmall δspoke ζret ηBalance θ a γ ξPart κ ζOrd b ∧
    2*(ζret+δspoke+Real.sqrt δspoke)+ηBalance+
      2*(2*θ+2*max a (4*γ)+2*ξPart+2*(δsmall+κ)+2*ζOrd+(1+2/rho)*etaGlobal)<globalCap ∧
    2*(ζret+10*θ)+ηBalance≤globalCap :=by
  intro a γ
  obtain ⟨hdel,ha,hγ,hRates⟩:=first_vortex_selected_deletion_local_rates d K (globalCap/2) rho tLocal etaLocal δsmall δspoke s θ lam eps ζOrd
    hd hK hs hθ hθ1 hlam heps hθs hlams hepsRate hζOrd hlocal ζret ηBalance ξPart κ b hζ hbal hξ hκ hb
  obtain ⟨hrow,hcol⟩:=first_vortex_separate_eta_coarse_global_rates globalCap rho tLocal etaLocal δsmall δspoke ζret ηBalance θ a γ ξPart κ ζOrd b etaGlobal
    hcap hrho hηLocal hroom hRates
  exact ⟨hdel,ha,hγ,hRates,hrow,hcol⟩
end Oberwolfach
