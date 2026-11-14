module

public import Oberwolfach.FirstVortexInnerSumSelectorRates

@[expose] public section
/-! The actual matching seed rates simultaneously fit the earlier global
robust budget and the later local summed-loss budget. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_selector_robust_rate_bridge
    (d K:ℕ) (s t θ θmax lam eps Δ Δmax ξPart δglobal rho eta c:ℝ)
    (hd:0<d) (hK:0<K) (hs:0<s) (ht:0<t) (hθ:0<θ) (hθ1:θ≤1)
    (hlam:0<lam) (heps:0<eps) (hlams:lam≤s) (hlamt:lam≤t)
    (hepsRate:3*eps≤lam*(θ/(100*(K:ℝ)^2))) (hΔ:Δ≤eps/8)
    (hθmax:θ≤θmax) (hΔmax:Δ≤Δmax) (hξ:ξPart≤t)
    (hRobust:∀θ' Δ' a γ ξ:ℝ,θ'≤θmax→Δ'≤Δmax→a≤t→γ≤t→ξ≤t→
      2*θ'+2*max a (4*γ)+2*ξ+5*Real.sqrt δglobal+2*Δ'+(1+2/rho)*eta<c/2048):
    let a:=min (lam/(10*(d:ℝ))) (θ/(200*(K:ℝ)^2))
    let γ:=min (eps/2) (min (1/2:ℝ) (min (lam/(10*(d:ℝ))) (lam/10)));
    0<a ∧ a≤s ∧ a≤t ∧ 0<γ ∧ γ≤s ∧ γ≤t ∧ Δ≤s ∧
      2*θ+2*max a (4*γ)+2*ξPart+5*Real.sqrt δglobal+2*Δ+(1+2/rho)*eta<c/2048 :=by
  intro a γ
  obtain ⟨ha,has,hg,hgs,hΔs⟩:=first_vortex_inner_sum_selector_rates d K s θ lam eps Δ
    hd hK hs hθ hθ1 hlam heps hlams hepsRate hΔ
  obtain ⟨_,hat,_,hgt,_⟩:=first_vortex_inner_sum_selector_rates d K t θ lam eps Δ
    hd hK ht hθ hθ1 hlam heps hlamt hepsRate hΔ
  exact ⟨ha,has,hat,hg,hgs,hgt,hΔs,hRobust θ Δ a γ ξPart hθmax hΔmax hat hgt hξ⟩
end Oberwolfach
