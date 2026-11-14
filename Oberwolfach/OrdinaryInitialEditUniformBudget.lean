module

public import Oberwolfach.OrdinaryVortexRootCoverCostFromGeometry

@[expose] public section
/-! A correction whose degree is a sufficiently small fraction of the host,
plus any fixed reservoir cost, fits both first-vortex inner domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach

theorem ordinary_initial_edit_uniform_budget
    (ε ρ₀ ζ:ℝ) (hε:0<ε) (hρ₀:0<ρ₀) (hζ:0<ζ):
    ∃ξ:ℝ,0<ξ ∧ ∀C:ℝ,0≤C→∃N:ℕ,1≤N ∧
    ∀n I B:ℝ,(N:ℝ)≤n→(ε/2)*n≤I→(ρ₀/8)*I≤B→
      0≤10*ξ*n+C ∧ 10*ξ*n+C≤ζ*I ∧ 10*ξ*n+C≤ζ*B :=by
  let r:ℝ:=min 1 (ρ₀/8)
  have hr:0<r:=lt_min (by norm_num) (by positivity)
  have hr1:r≤1:=min_le_left _ _
  have hrρ:r≤ρ₀/8:=min_le_right _ _
  let ξ:ℝ:=ζ*ε*r/80
  have hξ:0<ξ:=by dsimp [ξ];positivity
  refine ⟨ξ,hξ,?_⟩
  intro C hC
  have hscale:0<ζ*ε*r/4:=by positivity
  obtain ⟨N,hN⟩:=exists_nat_gt (C/(ζ*ε*r/4))
  refine ⟨max N 1,by omega,?_⟩
  intro n I B hn hI hB
  have hn0:0≤n:=le_trans (by positivity) hn
  have hNI:(N:ℝ)≤n:=by
    have hh:(N:ℝ)≤(max N 1:ℕ):=by exact_mod_cast (show N≤max N 1 by omega)
    exact hh.trans hn
  have hCn:C≤(ζ*ε*r/4)*n:=by
    have hh:C<(N:ℝ)*(ζ*ε*r/4):=(div_lt_iff₀ hscale).mp hN
    have hh':=(mul_le_mul_of_nonneg_right hNI hscale.le)
    nlinarith only [hh,hh']
  have hI0:0≤I:=le_trans (mul_nonneg (by positivity) hn0) hI
  have hB0:0≤B:=le_trans (mul_nonneg (by positivity) hI0) hB
  have hIref:(ε*r/2)*n≤I:=by
    have h1:=mul_le_mul_of_nonneg_left hr1 (show 0≤ε/2 by positivity)
    have h2:=mul_le_mul_of_nonneg_right h1 hn0
    nlinarith only [hI,h2]
  have hBref:(ε*r/2)*n≤B:=by
    have h1:=mul_le_mul_of_nonneg_right hrρ hI0
    have h2:=mul_le_mul_of_nonneg_left hI (show 0≤r by positivity)
    nlinarith only [hB,h1,h2]
  have hcost:10*ξ*n+C≤(ζ*ε*r/2)*n:=by
    dsimp [ξ]
    have hh:=mul_nonneg (show 0≤ζ*ε*r by positivity) hn0
    nlinarith only [hCn,hh]
  have hgoalI:(ζ*ε*r/2)*n≤ζ*I:=by
    have hh:=mul_le_mul_of_nonneg_left hIref hζ.le
    nlinarith only [hh]
  have hgoalB:(ζ*ε*r/2)*n≤ζ*B:=by
    have hh:=mul_le_mul_of_nonneg_left hBref hζ.le
    nlinarith only [hh]
  exact ⟨add_nonneg (by positivity) hC,hcost.trans hgoalI,hcost.trans hgoalB⟩
end Oberwolfach
