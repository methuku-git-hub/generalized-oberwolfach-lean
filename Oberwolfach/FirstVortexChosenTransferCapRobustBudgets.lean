module

public import Oberwolfach.MarkedVortexFixedMarginCorrectionCap
public import Oberwolfach.FirstVortexSharedRobustDualBudgetChoice

@[expose] public section
/-! Choose the level-transfer cap first, then choose the original robust
correction budgets beneath that cap. These choices precede the sample and
the later parent-event tolerance. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_chosen_transfer_cap_robust_budgets
    (r:ℕ) (κ α ω plo klo tstar kstar ζFixed thetaDeep levelEta B pstar etaBal x iota ρ₀ βfinal:ℝ)
    (hκ:0<κ) (hα:0<α) (hω:0<ω) (hplo:0<plo) (hklo:0<klo)
    (htstar:0<tstar) (hζFixed:0<ζFixed) (hθ:0<thetaDeep) (hη:0<levelEta)
    (hB:0 ≤ B) (hpstar:0<pstar) (hηBal:0<etaBal) (hx:0<x) (hiota:0 < iota)
    (hρ₀:0<ρ₀) (hβfinal:0<βfinal):
    let cCommon:=Classical.choose (marked_vortex_initial_common_from_parent_record r κ α ω plo klo hκ hα hω hplo hklo)
    let cDeep:=Classical.choose (marked_vortex_initial_deep_from_parent_record r (α/2) tstar kstar ζFixed thetaDeep B pstar hζFixed hθ hB hpstar)
    let cActive:=Classical.choose (marked_vortex_active_transfer_from_parent_fixed_margin r α tstar kstar ζFixed levelEta B pstar hζFixed hη hB hpstar htstar)
    let cBalance:=Classical.choose (marked_vortex_initial_record_balance_from_selected_parent r etaBal x iota hηBal hx hiota)
    let cBoundary:=Classical.choose (marked_vortex_initial_boundary_from_parent_record (r+12) x hx)
    let cap:=Classical.choose (marked_vortex_fixed_margin_correction_cap r κ α ω plo klo tstar kstar ζFixed thetaDeep levelEta B pstar etaBal x iota
      hκ hα hω hplo hklo htstar hζFixed hθ hη hB hpstar hηBal hx hiota);
    ∃rho eta ζmax Δmax δLoss εInner δglobal θmax t:ℝ,
      0<cap ∧ cap ≤ cCommon ∧ cap ≤ cDeep ∧ cap ≤ cActive ∧ cap ≤ cBalance ∧ cap ≤ cBoundary ∧
      (∀ζ:ℝ,0 ≤ ζ → ζ ≤ cap → (κ/2)/4+33*((r+4:ℝ)+1)^4*(2*B/pstar^(2*(r+4)+1))*ζ ≤ κ/4) ∧
      0<rho ∧ 0<eta ∧ 0<ζmax ∧ 0<Δmax ∧ 0<δLoss ∧ 0<εInner ∧
      0<δglobal ∧ 0<θmax ∧ 0<t ∧ eta ≤ rho ∧
      5*Real.sqrt δglobal ≤ δLoss ∧ δglobal ≤ (βfinal/100)^2 ∧
      10*θmax ≤ δglobal ∧ θmax ≤ min cap (1:ℝ)/1024 ∧
      δglobal+Real.sqrt δglobal ≤ min cap (1:ℝ)/1024 ∧ ζmax ≤ cap ∧
      (∀ζ:ℝ,0 ≤ ζ → ζ ≤ ζmax → ζ+δLoss<eta ∧
        rho+ζ+δLoss+εInner<ρ₀/(400*((r+4:ℕ):ℝ))) ∧
      (∀θ Δ a γ ξClass:ℝ,θ ≤ θmax → Δ ≤ Δmax → a ≤ t → γ ≤ t → ξClass ≤ t → 
        2*θ+2*max a (4*γ)+2*ξClass+5*Real.sqrt δglobal+2*Δ+(1+2/rho)*eta<min cap (1:ℝ)/2048) ∧
      ∀θ ζret refRate:ℝ,θ ≤ θmax → ζret ≤ min cap (1:ℝ)/1024 → refRate ≤ min cap (1:ℝ)/1024 → 
        2*(ζret+δglobal+Real.sqrt δglobal)+refRate+2*(min cap (1:ℝ)/1024)<min cap (1:ℝ)/2 ∧
        2*(ζret+10*θ)+refRate ≤ min cap (1:ℝ)/2 :=by
  intro cCommon cDeep cActive cBalance cBoundary cap
  obtain ⟨hcap,hC,hD,hA,hB',hBd,hpot⟩:=
    Classical.choose_spec (marked_vortex_fixed_margin_correction_cap r κ α ω plo klo tstar kstar ζFixed thetaDeep levelEta B pstar etaBal x iota
      hκ hα hω hplo hklo htstar hζFixed hθ hη hB hpstar hηBal hx hiota)
  obtain ⟨rho,eta,ζmax,Δmax,δLoss,εInner,δglobal,θmax,t,
    hrho,heta,hζ,hΔ,hLoss,hInner,hglobal,hθmax,ht,hetaR,hLossScale,hδbound,hθglobal,hθsmall,hδsum,hζcap,hBudget,hChange,hRows⟩:=
    first_vortex_shared_robust_dual_budget_choice r ρ₀ cap βfinal hρ₀ hcap hβfinal
  exact ⟨rho,eta,ζmax,Δmax,δLoss,εInner,δglobal,θmax,t,
    hcap,hC,hD,hA,hB',hBd,hpot,hrho,heta,hζ,hΔ,hLoss,hInner,hglobal,hθmax,ht,hetaR,
    hLossScale,hδbound,hθglobal,hθsmall,hδsum,hζcap,hBudget,hChange,hRows⟩
end Oberwolfach
