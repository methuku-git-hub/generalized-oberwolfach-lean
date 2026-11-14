module

public import Oberwolfach.FirstVortexEarlyDeletionRateBound
public import Oberwolfach.LongMatchingCorrectionSharedChangeCap

@[expose] public section
/-! The actual selector rates fit the previously chosen robust correction
budget, so its rim and spoke change graphs have a common cap. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_selector_robust_change_margins
    (d K r:ℕ) (ρ₀ cap rho eta ζmax Δmax δLoss εInner δglobal θmax t:ℝ)
    (θ lam eps ζ ξClass ζSpoke:ℝ)
    (hd:0<d) (hK:1≤K) (hlam:0≤lam) (hθ:θ≤θmax) (hθ1:θ≤1)
    (heps:3*eps≤lam*(θ/(100*(K:ℝ)^2))) (hζ:ζ≤eps/8) (hζ0:0≤ζ)
    (hlamcap:lam≤min t (3*min ζmax Δmax)) (hξ:ξClass≤t) (hSpoke:ζSpoke≤cap)
    (hBudget:∀z:ℝ,0≤z→z≤ζmax→z+δLoss<eta ∧
      rho+z+δLoss+εInner<ρ₀/(400*((r+4:ℕ):ℝ)))
    (hChange:∀θ' Δ a γ ξ:ℝ,θ'≤θmax→Δ≤Δmax→a≤t→γ≤t→ξ≤t→
      2*θ'+2*max a (4*γ)+2*ξ+5*Real.sqrt δglobal+2*Δ+(1+2/rho)*eta<cap):
    let a:=min (lam/(10*(d:ℝ))) (θ/(200*(K:ℝ)^2))
    let γ:=min (eps/2) (min (1/2:ℝ) (min (lam/(10*(d:ℝ))) (lam/10)));
    ζ+δLoss<eta ∧ rho+ζ+δLoss+εInner<ρ₀/(400*((r+4:ℕ):ℝ)) ∧
    2*θ+2*max a (4*γ)+2*ξClass+5*Real.sqrt δglobal+2*ζ+(1+2/rho)*eta<cap ∧
    ∃N:ℕ,∀n:ℕ,N≤n→∀{U:Type} [Fintype U] [DecidableEq U]
      (FR:SimpleGraph (Fin n)) (FS:SimpleGraph (Fin n⊕U)) (ηphys ηdel ηtype:ℝ),
      ηphys≤(2*θ+2*max a (4*γ)+2*ξClass+5*Real.sqrt δglobal)*n+
        (n:ℝ)^(3/5:ℝ)+ζ*n+2*(6*d+2:ℕ)→
      ηdel≤ζ*n→ηtype≤(1+2/rho)*eta*n+(n:ℝ)^(3/5:ℝ)→
      (∀v,(FR.degree v:ℝ)≤ηphys+ηdel+ηtype)→
      (∀z,(FS.degree z:ℝ)≤ζSpoke*n)→
      (∀v,(FR.degree v:ℝ)≤cap*n) ∧ (∀z,(FS.degree z:ℝ)≤cap*n) :=by
  intro a γ
  have hdR:1≤(d:ℝ):=by exact_mod_cast hd
  have hden:1≤10*(d:ℝ):=by linarith
  have hr:lam/(10*(d:ℝ))≤lam:=div_le_self hlam hden
  have ha:a≤t:=(min_le_left _ _).trans (hr.trans (hlamcap.trans (min_le_left _ _)))
  have hgRate:γ≤lam/(10*(d:ℝ)):=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hg:γ≤t:=hgRate.trans (hr.trans (hlamcap.trans (min_le_left _ _)))
  have hdel:=first_vortex_early_deletion_rate_bound lam θ eps ζ K hlam hθ1 hK heps hζ
  have hmin:lam≤3*min ζmax Δmax:=hlamcap.trans (min_le_right _ _)
  have hζmax:ζ≤ζmax:=by have hh:=min_le_left ζmax Δmax; linarith
  have hΔmax:ζ≤Δmax:=by have hh:=min_le_right ζmax Δmax; linarith
  obtain ⟨hbudget,hsupply⟩:=hBudget ζ hζ0 hζmax
  have hgap:=hChange θ ζ a γ ξClass hθ hΔmax ha hg hξ
  exact ⟨hbudget,hsupply,hgap,long_matching_correction_shared_change_cap d θ a γ ξClass δglobal ζ ζSpoke rho eta cap hSpoke hgap⟩
end Oberwolfach
