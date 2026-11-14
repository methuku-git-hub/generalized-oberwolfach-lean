module

public import Oberwolfach.FirstVortexOrderedAllHubRetentionBudget
public import Oberwolfach.FirstVortexRetentionShrinkAfterChoices

@[expose] public section
/-! Choose the actual global retention rate, the independent balance error,
then the common-event auxiliary scale in the order needed by the selector. -/
set_option autoImplicit false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_retention_balance_parameters
    (ε cap θ s c:ℝ) (r d:ℕ)
    (hε:0<ε) (hε1:ε≤1/4) (hcap:0<cap) (hθ:0<θ) (hs:0<s) (hc:0<c)
    (hd:1≤d) (hspacing:1/(d:ℝ)≤θ/1024):
    ∃ζret ζlocal ηBalance κaux:ℝ,
      0<ζret ∧ 0<ζlocal ∧ 0<ηBalance ∧ 0<κaux ∧
      ζret≤s ∧ ζret≤c/1024 ∧ ζret≤θ/4096 ∧
      ζlocal≤cap/128 ∧ ζret≤ζlocal*ε/2 ∧
      ηBalance≤s ∧ ηBalance≤c/1024 ∧
      κaux≤s ∧ κaux≤ζret ∧ κaux≤ηBalance/(8*((((r+4):ℕ):ℝ)+1)) ∧
    ∃Nret:ℕ,
      (∀n:ℕ,Nret≤n→∀q errOrd:ℝ,
        q≤1/(((((r+4):ℕ):ℝ))+1)→errOrd≤θ*n→
        (n:ℝ)*q/d+(((((r+4)+1)*d-1:ℕ):ℝ))*(2*((n:ℝ)^(3/4:ℝ)/d)+ζret*n)+errOrd≤4*θ*n) ∧
      ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
        [LinearOrder V] [DecidableEq U],
      ∀(G:SimpleGraph V) (D mm:ℕ) (β:ℝ) (Q:Vortex U G D β ε mm) (hmm:0<mm)
        (π:Equiv.Perm V) (σ:RawIntervalFamilyOutcome V U Γ Color) (g:Γ) (t:ℕ)
        (J:StartRetentionOutcome (rawStartHubSet π d σ g) t),
      RetainedRestrictionGood π d σ g t (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζret J→
      RetainedRestrictionLocalGood π d σ g t (Q.extendedVertices 1) Finset.univ ζlocal J :=by
  obtain ⟨ζold,ζlocal,hζold,hζlocal,hθζ,hlocalcap,hscale,hglobalcap,⟨Nret,hNret⟩,hRet⟩:=
    first_vortex_ordered_all_hub_retention_budget ε cap θ (r+4) d hε hε1 hcap hθ (by omega) hd hspacing
  let upper:=min s (c/1024)
  have hupper:0<upper:=by dsimp [upper];positivity
  obtain ⟨ζret,hζret,hζupper,hζold',hNret',hRet'⟩:=
    first_vortex_retention_shrink_after_choices ε θ ζold ζlocal (r+4) d Nret hζold hNret hRet upper hupper
  have hζs:ζret≤s:=hζupper.trans (min_le_left _ _)
  have hζc:ζret≤c/1024:=hζupper.trans (min_le_right _ _)
  let ηBalance:=upper/2
  have hbal:0<ηBalance:=by dsimp [ηBalance];positivity
  have hbals:ηBalance≤s:=by dsimp [ηBalance,upper];have hh:=min_le_left s (c/1024);linarith
  have hbalc:ηBalance≤c/1024:=by dsimp [ηBalance,upper];have hh:=min_le_right s (c/1024);linarith
  let κaux:=min s (min ζret (ηBalance/(8*((((r+4):ℕ):ℝ)+1))))
  have hκ:0<κaux:=by dsimp [κaux];positivity
  refine ⟨ζret,ζlocal,ηBalance,κaux,hζret,hζlocal,hbal,hκ,hζs,hζc,hζold'.trans hθζ,
    hlocalcap,hζold'.trans hscale,hbals,hbalc,min_le_left _ _,
    (min_le_right _ _).trans (min_le_left _ _),(min_le_right _ _).trans (min_le_right _ _),Nret,hNret',hRet'⟩
end Oberwolfach
