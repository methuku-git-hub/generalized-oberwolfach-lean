module

public import Oberwolfach.FirstVortexGlobalThenLocalParameterHierarchy
public import Oberwolfach.FirstVortexSelectorRobustRateBridge
public import Oberwolfach.FirstVortexAmbientGlobalEventualBudgets

@[expose] public section
/-! Instantiate the early global supply and robust-change inequalities with
the actual selector seed and deletion rates. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach

theorem first_vortex_actual_selector_global_budgets
    (r d K:ℕ) (ρ₀ cap β rho eta ζmax Δmax δLoss εInner δglobal θmax t:ℝ)
    (s θ lam eps Δ ξPart ζret ηBalance κPack:ℝ)
    (hData:FirstVortexAmbientGlobalData r ρ₀ cap β rho eta ζmax Δmax δLoss εInner δglobal θmax t)
    (hd:0<d) (hK:1≤K) (hs:0<s) (hθ:0<θ) (hθ1:θ≤1) (hθmax:θ≤θmax)
    (hlam:0<lam) (heps:0<eps) (hlams:lam≤s)
    (hlamcap:lam≤min t (3*min ζmax Δmax))
    (hepsRate:3*eps≤lam*(θ/(100*(K:ℝ)^2))) (hΔ0:0≤Δ) (hΔ:Δ≤eps/8)
    (hξ:ξPart≤t) (hζret:ζret≤min cap (1:ℝ)/1024)
    (hbal:ηBalance≤min cap (1:ℝ)/1024) (hκ:κPack≤min cap (1:ℝ)/1024):
    let c:=min cap (1:ℝ)
    let a:=min (lam/(10*(d:ℝ))) (θ/(200*(K:ℝ)^2))
    let γ:=min (eps/2) (min (1/2:ℝ) (min (lam/(10*(d:ℝ))) (lam/10)));
    Δ+δLoss<eta ∧ rho+Δ+δLoss+εInner<ρ₀/(400*((r+4:ℕ):ℝ)) ∧
    0<a ∧ a≤s ∧ a≤t ∧ 0<γ ∧ γ≤s ∧ γ≤t ∧ Δ≤s ∧
    ∃N:ℕ,∀n:ℕ,N≤n→
      2*(ζret*n+(δglobal*n+(Real.sqrt δglobal*n+1)))+
        (ηBalance*n+2*(((2*θ+2*max a (4*γ)+2*ξPart)*n+2*(δglobal*n+(κPack*n+1)))+
          (n:ℝ)^(3/5:ℝ)+Δ*n+2*(6*d+2:ℕ)+Δ*n+((1+2/rho)*eta*n+1)))≤(c/2)*n ∧
      2*(ζret*n+10*θ*n)+ηBalance*n≤(c/2)*n :=by
  intro c a γ
  obtain ⟨hrho,heta,hζ,hΔmax,hLoss,hInner,hδ,hθmax0,ht,hetaR,hInnerδ,hLossScale,hδbound,hθglobal,hθsmall,hδsum,hζcap,hBudget,hChange,hRows,hAmbient⟩:=hData
  have hlamt:lam≤t:=hlamcap.trans (min_le_left _ _)
  have hlamz:lam≤3*min ζmax Δmax:=hlamcap.trans (min_le_right _ _)
  have hΔlam:=first_vortex_early_deletion_rate_bound lam θ eps Δ K hlam.le hθ1 hK hepsRate hΔ
  have hΔζ:Δ≤ζmax:=by have hh:=min_le_left ζmax Δmax;linarith
  have hΔΔ:Δ≤Δmax:=by have hh:=min_le_right ζmax Δmax;linarith
  obtain ⟨hbudget,hsupply⟩:=hBudget Δ hΔ0 hΔζ
  obtain ⟨ha,has,hat,hγ,hγs,hγt,hΔs,hbase⟩:=
    first_vortex_selector_robust_rate_bridge d K s t θ θmax lam eps Δ Δmax ξPart δglobal rho eta c
      hd (by omega) hs ht hθ hθ1 hlam heps hlams hlamt hepsRate hΔ hθmax hΔΔ hξ hChange
  have hc:0<c:=by dsimp [c];have hh:=hδsum;have hsqrt:=Real.sqrt_nonneg δglobal;linarith
  have hcol:2*(ζret+10*θ)+ηBalance≤c/2:=(hRows θ ζret ηBalance hθmax hζret hbal).2
  obtain ⟨N,hN⟩:=first_vortex_ambient_global_eventual_budgets d c ζret δglobal ηBalance θ a γ ξPart κPack Δ rho eta
    hc hδ.le hδsum hζret hbal hκ hbase hcol
  exact ⟨hbudget,hsupply,ha,has,hat,hγ,hγs,hγt,hΔs,N,hN⟩
end Oberwolfach
