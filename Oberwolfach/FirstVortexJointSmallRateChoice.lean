module

public import Oberwolfach.FirstVortexSplitChangeRateChoice

@[expose] public section
/-! Choose the matching correction rate and then a smaller common rate for
the global, local, and boundary margins. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_joint_small_rate_choice
    (cap rho tLocal upper:ℝ) (hcap:0<cap) (hrho:0<rho) (htLocal:0<tLocal) (hupper:0<upper):
    ∃eta s:ℝ,0<eta ∧ eta≤tLocal ∧ 0<s ∧ s≤upper ∧
    ∀ζret δspoke ηBalance θ a γ ξPart δsmall κ Δ b αAssign:ℝ,
      ζret≤s→δspoke≤s→Real.sqrt δspoke≤s→ηBalance≤s→θ≤s→a≤s→γ≤s→
      ξPart≤s→δsmall≤s→κ≤s→Δ≤s→b≤s→αAssign≤s→
      2*θ+2*max a (4*γ)+2*ξPart≤tLocal ∧
      b+2*max a γ+αAssign/16+κ<tLocal ∧ 2*Δ<tLocal ∧
      Δ+2*(b+2*max a γ+αAssign/16+κ)<eta ∧ ζret≤tLocal ∧ ηBalance≤tLocal ∧
      2*(ζret+δspoke+Real.sqrt δspoke)+ηBalance+
        2*(2*θ+2*max a (4*γ)+2*ξPart+2*(δsmall+κ)+2*Δ+(1+2/rho)*eta)<cap ∧
      2*(ζret+10*θ)+ηBalance≤cap :=by
  obtain ⟨g,hg,hglobal⟩:=first_vortex_split_change_rate_choice cap rho hcap hrho
  let eta:=min (tLocal/2) (g/2)
  have heta:0<eta:=by dsimp [eta];positivity
  have hetaLocal:eta≤tLocal:=by dsimp [eta];have h:=min_le_left (tLocal/2) (g/2);linarith
  have hetaG:eta≤g:=by dsimp [eta];have h:=min_le_right (tLocal/2) (g/2);linarith
  let s:=min (upper/2) (min (tLocal/100) (min (eta/100) (g/2)))
  have hs:0<s:=by dsimp [s];positivity
  have hsUpper:s≤upper:=by dsimp [s];have h:=min_le_left (upper/2) (min (tLocal/100) (min (eta/100) (g/2)));linarith
  have hsLocal:s≤tLocal/100:=by
    dsimp [s]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hsEta:s≤eta/100:=by
    dsimp [s]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsG:s≤g:=by
    dsimp [s]
    have hh: min (upper/2) (min (tLocal/100) (min (eta/100) (g/2)))≤g/2:=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    linarith
  refine ⟨eta,s,heta,hetaLocal,hs,hsUpper,?_⟩
  intro ζret δspoke ηBalance θ a γ ξPart δsmall κ Δ b αAssign hζ hδ hsqrt hbal hθ ha hγ hξ hsmall hκ hΔ hb hα
  have hmax4:max a (4*γ)≤4*s:=max_le (by linarith) (by linarith)
  have hmax:max a γ≤s:=max_le ha hγ
  have hA:2*θ+2*max a (4*γ)+2*ξPart≤tLocal:=by linarith
  have hB:b+2*max a γ+αAssign/16+κ<tLocal:=by linarith
  have hE:2*Δ<tLocal:=by linarith
  have hLocal:Δ+2*(b+2*max a γ+αAssign/16+κ)<eta:=by linarith
  have hret:ζret≤tLocal:=by linarith
  have hbalance:ηBalance≤tLocal:=by linarith
  obtain ⟨hrow,hcol⟩:=hglobal ζret δspoke ηBalance θ a γ ξPart δsmall κ Δ eta
    (hζ.trans hsG) (hδ.trans hsG) (hsqrt.trans hsG) (hbal.trans hsG) (hθ.trans hsG) (ha.trans hsG)
    (hγ.trans hsG) (hξ.trans hsG) (hsmall.trans hsG) (hκ.trans hsG) (hΔ.trans hsG) hetaG
  exact ⟨hA,hB,hE,hLocal,hret,hbalance,hrow,hcol⟩
end Oberwolfach
