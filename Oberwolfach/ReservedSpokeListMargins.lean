module

public import Oberwolfach.ReservedSpokeResidualParameters

@[expose] public section
/-! The reserved-spoke extension and residual constants can be fixed before θ. -/
set_option autoImplicit false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach

theorem reserved_spoke_list_margins (α ρ:ℝ) (hα:0<α) (hρ:0<ρ) (d:ℕ):
    ∃β lam ζ βres θ δ:ℝ,
      0<β ∧ 0<lam ∧ 0<ζ ∧ 0<βres ∧ βres≤1 ∧
      0<θ ∧ θ≤1/100 ∧ 0<δ ∧ 10*θ≤δ ∧ δ≤(βres/100)^2 ∧
      lam+2*ζ≤β ∧ βres≤lam/2 ∧
      ∃N:ℕ,∀n:ℕ,N≤n→
        (n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤α*(ρ/200)^2*n ∧
        β*n+(n:ℝ)^(3/4:ℝ)≤α*(ρ/200)^2*n*(1/100:ℝ):=by
  let c:ℝ:=α*(ρ/200)^2
  have hc:0<c:=by dsimp [c];positivity
  let β:ℝ:=min 1 (c/400)
  let lam:ℝ:=β/2
  let ζ:ℝ:=β/8
  let βres:ℝ:=β/4
  have hβ:0<β:=lt_min (by norm_num) (by positivity)
  have hβ1:β≤1:=min_le_left _ _
  have hβc:β≤c/400:=min_le_right _ _
  have hlam:0<lam:=by dsimp [lam];positivity
  have hζ:0<ζ:=by dsimp [ζ];positivity
  have hres:0<βres:=by dsimp [βres];positivity
  have hres1:βres≤1:=by dsimp [βres];linarith
  obtain ⟨θ,δ,hθ,hθmax,hδ,hθδ,hδres⟩:=reserved_spoke_residual_parameter_choice βres hres hres1
  obtain ⟨N₀,hN₀⟩:=eventually_three_quarters_and_constant_le_linear c (2*(2*((3*d:ℕ):ℝ)+1)) hc
  obtain ⟨N₁,hN₁⟩:=eventually_three_quarters_and_constant_le_linear (c/400) 0 (by positivity)
  refine ⟨β,lam,ζ,βres,θ,δ,hβ,hlam,hζ,hres,hres1,hθ,hθmax,hδ,hθδ,hδres,?_,?_,max N₀ N₁,?_⟩
  · dsimp [lam,ζ];linarith
  · dsimp [βres,lam];linarith
  · intro n hn
    have h0:=hN₀ n (by omega)
    have h1:=hN₁ n (by omega)
    have hnR:(0:ℝ)≤n:=by positivity
    have hh:=mul_le_mul_of_nonneg_right hβc hnR
    dsimp only [c] at *
    constructor
    · exact h0
    · nlinarith
end Oberwolfach
