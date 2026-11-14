module

public import Oberwolfach.FirstVortexSelectorRobustChangeMargins
public import Oberwolfach.LongSharedRimSpokeEventualBudget

@[expose] public section
/-! The concrete selector rates satisfy both the global robust-change cap
and the row and column budgets on a common sufficiently large order. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_selector_shared_robust_margins
    (d K r:ℕ) (ρ₀ cap rho eta ζmax Δmax δLoss εInner δglobal θmax t:ℝ)
    (θ lam eps ζ ξClass ζret refRate:ℝ)
    (hd:0<d) (hK:1≤K) (hcap:0<cap) (hlam:0≤lam) (hθ:θ≤θmax) (hθ1:θ≤1)
    (heps:3*eps≤lam*(θ/(100*(K:ℝ)^2))) (hζ:ζ≤eps/8) (hζ0:0≤ζ)
    (hlamcap:lam≤min t (3*min ζmax Δmax)) (hξ:ξClass≤t):
    let c:=min cap (1:ℝ);
    (∀z:ℝ,0≤z→z≤ζmax→z+δLoss<eta ∧
      rho+z+δLoss+εInner<ρ₀/(400*((r+4:ℕ):ℝ)))→
    (∀θ' Δ a γ ξ:ℝ,θ'≤θmax→Δ≤Δmax→a≤t→γ≤t→ξ≤t→
      2*θ'+2*max a (4*γ)+2*ξ+5*Real.sqrt δglobal+2*Δ+(1+2/rho)*eta<c/2048)→
    (∀θ' ζret' refRate':ℝ,θ'≤θmax→ζret'≤c/1024→ refRate'≤c/1024→
      2*(ζret'+δglobal+Real.sqrt δglobal)+refRate'+2*(c/1024)<c/2 ∧
      2*(ζret'+10*θ')+refRate'≤c/2)→
    ζret≤c/1024→ refRate≤c/1024→
    let a:=min (lam/(10*(d:ℝ))) (θ/(200*(K:ℝ)^2))
    let γ:=min (eps/2) (min (1/2:ℝ) (min (lam/(10*(d:ℝ))) (lam/10)));
    ζ+δLoss<eta ∧ rho+ζ+δLoss+εInner<ρ₀/(400*((r+4:ℕ):ℝ)) ∧
    ∃N:ℕ,∀n:ℕ,N≤n→∀lossRow lossCol ε ηphys ηdel ηtype:ℝ,
      lossRow≤ζret*n→lossCol≤ζret*n→ε≤refRate*n→
      ηphys≤(2*θ+2*max a (4*γ)+2*ξClass+5*Real.sqrt δglobal)*n+
        (n:ℝ)^(3/5:ℝ)+ζ*n+2*(6*d+2:ℕ)→
      ηdel≤ζ*n→ηtype≤(1+2/rho)*eta*n+(n:ℝ)^(3/5:ℝ)→
      ηphys+ηdel+ηtype≤cap*n ∧ c/2≤cap ∧
      2*(lossRow+(δglobal*n+(Real.sqrt δglobal*n+1)))+(ε+2*(ηphys+ηdel+ηtype))≤(c/2)*n ∧
      2*(lossCol+10*θ*n)+ε≤(c/2)*n :=by
  intro c hBudget hChange hRows hret href a γ
  have hc:0<c:=by dsimp [c];positivity
  have hMargins:=first_vortex_selector_robust_change_margins d K r ρ₀ (c/2048) rho eta ζmax Δmax δLoss εInner δglobal θmax t
    θ lam eps ζ ξClass 0 hd hK hlam hθ hθ1 heps hζ hζ0 hlamcap hξ (by positivity) hBudget hChange
  dsimp only at hMargins
  obtain ⟨hbudget,hsupply,hgap,_⟩:=hMargins
  obtain ⟨hrow,hcol⟩:=hRows θ ζret refRate hθ hret href
  exact ⟨hbudget,hsupply,long_shared_rim_spoke_eventual_budget d θ a γ ξClass δglobal ζ rho eta ζret refRate cap hcap hgap hrow hcol⟩
end Oberwolfach
