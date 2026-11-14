module

public import Oberwolfach.MarkedVortexLocalizedCorrectionCap
public import Oberwolfach.MarkedVortexFixedMarginCorrectionCap
public import Oberwolfach.FirstVortexSharedRobustDualBudgetChoice
public import Oberwolfach.FirstVortexSelectorSharedRobustMargins

@[expose] public section
/-! Choose the level-transfer cap first, then choose the original robust
correction budgets beneath that cap. These choices precede the sample and
the later parent-event tolerance. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_transfer_stable_localized_cap_aligned
    (r:ℕ) (κ α ω plo klo tstar kstar ζFixed thetaDeep levelEta B pstar x ρ₀ βfinal:ℝ)
    (hκ:0<κ) (hα:0<α) (hω:0<ω) (hplo:0<plo) (hklo:0<klo)
    (htstar:0<tstar) (hζFixed:0<ζFixed) (hθ:0<thetaDeep) (hη:0<levelEta)
    (hB:0  ≤  B) (hpstar:0<pstar) (hx:0<x)
    (hρ₀:0<ρ₀) (hβfinal:0<βfinal) (upper:ℝ) (hupper:0<upper):
    let cCommon:=Classical.choose (marked_vortex_initial_common_from_parent_record r κ α ω plo klo hκ hα hω hplo hklo)
    let cDeep:=Classical.choose (marked_vortex_initial_deep_from_parent_record r (α/2) tstar kstar ζFixed thetaDeep B pstar hζFixed hθ hB hpstar)
    let cActive:=Classical.choose (marked_vortex_active_transfer_from_parent_fixed_margin r α tstar kstar ζFixed levelEta B pstar hζFixed hη hB hpstar htstar)
    let cBalance:=Classical.choose (marked_inner_deep_balance_ordered_caps (r+4) x hx)
    let cBoundary:=Classical.choose (marked_vortex_initial_boundary_from_parent_record (r+12) x hx)
    let transferCap:=Classical.choose (marked_vortex_localized_correction_cap r κ α ω plo klo tstar kstar ζFixed thetaDeep levelEta B pstar x
      hκ hα hω hplo hklo htstar hζFixed hθ hη hB hpstar hx)
    let cap:=min transferCap upper;
    ∃rho eta ζmax Δmax δLoss εInner δglobal θmax t:ℝ,
      0<cap ∧ cap  ≤  upper ∧ cap  ≤  transferCap ∧ cap  ≤  cCommon ∧ cap  ≤  cDeep ∧ cap  ≤  cActive ∧ cap  ≤  cBalance ∧ cap  ≤  cBoundary ∧
      (∀ζ:ℝ,0  ≤  ζ  →  ζ  ≤  cap  →  (κ/2)/4+33*((r+4:ℝ)+1)^4*(2*B/pstar^(2*(r+4)+1))*ζ  ≤  κ/4) ∧
      0<rho ∧ 0<eta ∧ 0<ζmax ∧ 0<Δmax ∧ 0<δLoss ∧ 0<εInner ∧
      0<δglobal ∧ 0<θmax ∧ 0<t ∧ eta  ≤  rho ∧
      5*Real.sqrt δglobal  ≤  δLoss ∧ δglobal  ≤  (βfinal/100)^2 ∧
      10*θmax  ≤  δglobal ∧ θmax  ≤  min cap (1:ℝ)/1024 ∧
      δglobal+Real.sqrt δglobal  ≤  min cap (1:ℝ)/1024 ∧ ζmax  ≤  cap ∧
      (∀ζ:ℝ,0  ≤  ζ  →  ζ  ≤  ζmax  →  ζ+δLoss<eta ∧
        rho+ζ+δLoss+εInner<ρ₀/(400*((r+4:ℕ):ℝ))) ∧
      (∀θ Δ a γ ξClass:ℝ,θ  ≤  θmax  →  Δ  ≤  Δmax  →  a  ≤  t  →  γ  ≤  t  →  ξClass  ≤  t  → 
        2*θ+2*max a (4*γ)+2*ξClass+5*Real.sqrt δglobal+2*Δ+(1+2/rho)*eta<min cap (1:ℝ)/2048) ∧
      (∀θ ζret refRate:ℝ,θ  ≤  θmax  →  ζret  ≤  min cap (1:ℝ)/1024  →  refRate  ≤  min cap (1:ℝ)/1024  → 
        2*(ζret+δglobal+Real.sqrt δglobal)+refRate+2*(min cap (1:ℝ)/1024)<min cap (1:ℝ)/2 ∧
        2*(ζret+10*θ)+refRate  ≤  min cap (1:ℝ)/2) ∧
      ∀(d K:ℕ) (θ lam eps ζ ξClass ζret refRate:ℝ),
        0<d  →  1  ≤  K  →  0  ≤  lam  →  θ  ≤  θmax  →  θ  ≤  1  → 
        3*eps  ≤  lam*(θ/(100*(K:ℝ)^2))  →  ζ  ≤  eps/8  →  0  ≤  ζ  → 
        lam  ≤  min t (3*min ζmax Δmax)  →  ξClass  ≤  t  → 
        ζret  ≤  min cap (1:ℝ)/1024  →  refRate  ≤  min cap (1:ℝ)/1024  → 
        let a:=min (lam/(10*(d:ℝ))) (θ/(200*(K:ℝ)^2))
        let γ:=min (eps/2) (min (1/2:ℝ) (min (lam/(10*(d:ℝ))) (lam/10)));
        ζ+δLoss<eta ∧ rho+ζ+δLoss+εInner<ρ₀/(400*((r+4:ℕ):ℝ)) ∧
        ∃N:ℕ,∀n:ℕ,N  ≤  n  →  ∀lossRow lossCol ε ηphys ηdel ηtype:ℝ,
          lossRow  ≤  ζret*n  →  lossCol  ≤  ζret*n  →  ε  ≤  refRate*n  → 
          ηphys  ≤  (2*θ+2*max a (4*γ)+2*ξClass+5*Real.sqrt δglobal)*n+
            (n:ℝ)^(3/5:ℝ)+ζ*n+2*(6*d+2:ℕ)  → 
          ηdel  ≤  ζ*n  →  ηtype  ≤  (1+2/rho)*eta*n+(n:ℝ)^(3/5:ℝ)  → 
          ηphys+ηdel+ηtype  ≤  cap*n ∧ min cap (1:ℝ)/2  ≤  cap ∧
          2*(lossRow+(δglobal*n+(Real.sqrt δglobal*n+1)))+(ε+2*(ηphys+ηdel+ηtype))  ≤  (min cap (1:ℝ)/2)*n ∧
          2*(lossCol+10*θ*n)+ε  ≤  (min cap (1:ℝ)/2)*n :=by
  intro cCommon cDeep cActive cBalance cBoundary transferCap cap
  obtain ⟨htransfer,hC0,hD0,hA0,hB0,hBd0,hpot0⟩:=
    Classical.choose_spec (marked_vortex_localized_correction_cap r κ α ω plo klo tstar kstar ζFixed thetaDeep levelEta B pstar x
      hκ hα hω hplo hklo htstar hζFixed hθ hη hB hpstar hx)
  have hcap:0<cap:=by dsimp [cap];positivity
  have htransferCap:cap  ≤  transferCap:=min_le_left _ _
  have hup:cap  ≤  upper:=min_le_right _ _
  have hC:=htransferCap.trans hC0
  have hD:=htransferCap.trans hD0
  have hA:=htransferCap.trans hA0
  have hB':=htransferCap.trans hB0
  have hBd:=htransferCap.trans hBd0
  have hpot:∀ζ:ℝ,0 ≤ ζ → ζ ≤ cap → (κ/2)/4+33*((r+4:ℝ)+1)^4*(2*B/pstar^(2*(r+4)+1))*ζ ≤ κ/4:=by
    intro ζ hζ hζcap
    exact hpot0 ζ hζ (hζcap.trans htransferCap)
  obtain ⟨rho,eta,ζmax,Δmax,δLoss,εInner,δglobal,θmax,t,
    hrho,heta,hζ,hΔ,hLoss,hInner,hglobal,hθmax,ht,hetaR,hLossScale,hδbound,hθglobal,hθsmall,hδsum,hζcap,hBudget,hChange,hRows⟩:=
    first_vortex_shared_robust_dual_budget_choice r ρ₀ cap βfinal hρ₀ hcap hβfinal
  refine ⟨rho,eta,ζmax,Δmax,δLoss,εInner,δglobal,θmax,t,
    hcap,hup,htransferCap,hC,hD,hA,hB',hBd,hpot,hrho,heta,hζ,hΔ,hLoss,hInner,hglobal,hθmax,ht,hetaR,
    hLossScale,hδbound,hθglobal,hθsmall,hδsum,hζcap,hBudget,hChange,hRows,?_⟩
  intro d K θ lam eps ζ ξClass ζret refRate hd hK hlam hθ hθ1 heps hζ0 hζpos hlamcap hξ hret href
  exact first_vortex_selector_shared_robust_margins d K r ρ₀ cap rho eta ζmax Δmax δLoss εInner δglobal θmax t
    θ lam eps ζ ξClass ζret refRate hd hK hcap hlam hθ hθ1 heps hζ0 hζpos hlamcap hξ hBudget hChange hRows hret href
end Oberwolfach
