module

public import Oberwolfach.FirstVortexSplitChangeRateChoice

@[expose] public section
/-! Choose the global forced-load and spoke scales before the later local
balance scale. The assignment parameter is absent from the local estimates. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_ordered_geometry_rates
    (cap rho upper:ℝ) (hcap:0<cap) (hrho:0<rho) (hupper:0<upper):
    ∃δsmall δspoke:ℝ,0<δsmall ∧ 0<δspoke ∧ δsmall≤upper ∧
    ∀tLocal:ℝ,0<tLocal→∃eta s:ℝ,0<eta ∧ eta≤tLocal ∧ 0<s ∧ s≤upper ∧
    ∀ζret ηBalance θ a γ ξPart κ Δ b:ℝ,
      ζret≤s→ηBalance≤s→θ≤s→a≤s→γ≤s→ξPart≤s→κ≤s→Δ≤s→b≤s→
      δsmall+κ≤Real.sqrt δspoke ∧
      2*θ+2*max a (4*γ)+2*ξPart≤tLocal ∧
      b+2*max a γ+κ<tLocal ∧ 2*Δ<tLocal ∧
      Δ+2*(b+2*max a γ+κ)<eta ∧ ζret≤tLocal ∧ ηBalance≤tLocal ∧
      2*(ζret+δspoke+Real.sqrt δspoke)+ηBalance+
        2*(2*θ+2*max a (4*γ)+2*ξPart+2*(δsmall+κ)+2*Δ+(1+2/rho)*eta)<cap ∧
      2*(ζret+10*θ)+ηBalance≤cap :=by
  obtain ⟨g,hg,hglobal⟩:=first_vortex_split_change_rate_choice cap rho hcap hrho
  let v:=min (g/16) (min (upper/2) (1/2))
  have hv:0<v:=by dsimp [v];positivity
  have hvg:v≤g/16:=min_le_left _ _
  have hvu:v≤upper/2:=(min_le_right _ _).trans (min_le_left _ _)
  have hv1:v≤1/2:=(min_le_right _ _).trans (min_le_right _ _)
  let δsmall:=v/4
  let δspoke:=v^2
  have hsmall:0<δsmall:=by dsimp [δsmall];positivity
  have hspoke:0<δspoke:=by dsimp [δspoke];positivity
  have hsmallU:δsmall≤upper:=by dsimp [δsmall];linarith
  have hsmallG:δsmall≤g:=by dsimp [δsmall];linarith
  have hspokeG:δspoke≤g:=by dsimp [δspoke];nlinarith
  have hsqrt:Real.sqrt δspoke=v:=by dsimp [δspoke];rw [Real.sqrt_sq_eq_abs,abs_of_pos hv]
  have hsqrtG:Real.sqrt δspoke≤g:=by rw [hsqrt];linarith
  refine ⟨δsmall,δspoke,hsmall,hspoke,hsmallU,?_⟩
  intro tLocal htLocal
  let eta:=min (tLocal/2) (g/2)
  have heta:0<eta:=by dsimp [eta];positivity
  have hetaLocal:eta≤tLocal:=by dsimp [eta];have h:=min_le_left (tLocal/2) (g/2);linarith
  have hetaG:eta≤g:=by dsimp [eta];have h:=min_le_right (tLocal/2) (g/2);linarith
  let s:=min (upper/2) (min (tLocal/100) (min (eta/100) (min (g/2) δsmall)))
  have hs:0<s:=by dsimp [s];positivity
  have hsUpper:s≤upper:=by dsimp [s];have h:=min_le_left (upper/2) (min (tLocal/100) (min (eta/100) (min (g/2) δsmall)));linarith
  have hsLocal:s≤tLocal/100:=(min_le_right _ _).trans (min_le_left _ _)
  have hsEta:s≤eta/100:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsG:s≤g:=by
    have hh:s≤g/2:=(min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    linarith
  have hsSmall:s≤δsmall:=(min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨eta,s,heta,hetaLocal,hs,hsUpper,?_⟩
  intro ζret ηBalance θ a γ ξPart κ Δ b hζ hbal hθ ha hγ hξ hκ hΔ hb
  have hsqrtScale:δsmall+κ≤Real.sqrt δspoke:=by
    rw [hsqrt]
    dsimp [δsmall] at hsSmall ⊢
    linarith
  have hmax4:max a (4*γ)≤4*s:=max_le (by linarith) (by linarith)
  have hmax:max a γ≤s:=max_le ha hγ
  have hA:2*θ+2*max a (4*γ)+2*ξPart≤tLocal:=by linarith
  have hB:b+2*max a γ+κ<tLocal:=by linarith
  have hE:2*Δ<tLocal:=by linarith
  have hLocal:Δ+2*(b+2*max a γ+κ)<eta:=by linarith
  have hret:ζret≤tLocal:=by linarith
  have hbalance:ηBalance≤tLocal:=by linarith
  obtain ⟨hrow,hcol⟩:=hglobal ζret δspoke ηBalance θ a γ ξPart δsmall κ Δ eta
    (hζ.trans hsG) hspokeG hsqrtG (hbal.trans hsG) (hθ.trans hsG) (ha.trans hsG)
    (hγ.trans hsG) (hξ.trans hsG) hsmallG (hκ.trans hsG) (hΔ.trans hsG) hetaG
  exact ⟨hsqrtScale,hA,hB,hE,hLocal,hret,hbalance,hrow,hcol⟩
end Oberwolfach
