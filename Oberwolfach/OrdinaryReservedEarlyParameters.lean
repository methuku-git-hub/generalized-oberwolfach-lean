module

public import Oberwolfach.OrdinaryReservedListRateChoice
public import Oberwolfach.OrdinaryPlacementOriginalSpacingRates

@[expose] public section
/-! Select positive selected-list rates and the placement tolerance before
choosing the matching error θ. -/
set_option autoImplicit false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach

theorem ordinary_reserved_early_parameters
    (βfreq ρ₀ γ cap:ℝ) (hβfreq:0<βfreq) (hρ₀:0<ρ₀) (hγ:0<γ) (hcap:0<cap):
    ∃smin pstar β lam ζ δ θ:ℝ,
      smin=βfreq/200 ∧ 0<smin ∧
      pstar=(min 1 (ρ₀*smin))/2 ∧ 0<pstar ∧ 2*pstar≤1 ∧ 2*pstar≤ρ₀*smin ∧
      0<β ∧ β≤1 ∧ 0<lam ∧ 0<ζ ∧ lam+2*ζ≤β ∧
      0<δ ∧ δ≤((lam/2)/100)^2 ∧ 5*Real.sqrt δ≤cap ∧
      0<θ ∧ θ≤1/100 ∧ θ≤δ/8 ∧
      ∀d:ℕ,∃N:ℕ,∀n:ℕ,N≤n→
        (n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤γ*pstar^2*n ∧
        β*n+(n:ℝ)^(3/4:ℝ)≤γ*pstar^2*n*smin :=by
  let smin:ℝ:=βfreq/200
  let pstar:ℝ:=(min 1 (ρ₀*smin))/2
  have hs:0<smin:=by dsimp [smin];positivity
  have hp:0<pstar:=by dsimp [pstar];positivity
  have hp1:2*pstar≤1:=by dsimp [pstar];linarith [min_le_left (1:ℝ) (ρ₀*smin)]
  have hpρ:2*pstar≤ρ₀*smin:=by dsimp [pstar];linarith [min_le_right (1:ℝ) (ρ₀*smin)]
  obtain ⟨β,lam,ζ,hβ,hβ1,hlam,hζ,hbudget,hN⟩:=ordinary_reserved_list_rate_choice γ pstar smin hγ hp hs
  obtain ⟨δ,hδ,hδsmall,hδcap⟩:=ordinary_placement_delta_from_target_rate (lam/2) cap (by positivity) hcap
  let θ:ℝ:=min (δ/16) (1/200:ℝ)
  have hθ:0<θ:=by dsimp [θ];positivity
  have hθ1:θ≤1/100:=(min_le_right _ _).trans (by norm_num)
  have hθδ:θ≤δ/8:=(min_le_left _ _).trans (by linarith)
  exact ⟨smin,pstar,β,lam,ζ,δ,θ,rfl,hs,rfl,hp,hp1,hpρ,hβ,hβ1,hlam,hζ,hbudget,hδ,hδsmall,hδcap,hθ,hθ1,hθδ,hN⟩
end Oberwolfach
