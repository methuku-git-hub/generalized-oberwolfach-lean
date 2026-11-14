module

public import Oberwolfach.ResidualLongErrorBudgetBelow

@[expose] public section
/-! After the vortex scale, local transfer cap, θ and spacing are fixed,
choose one global retention tolerance that also gives the needed all-hub
first-active tolerance and the full residual-size estimate. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach

theorem first_vortex_ordered_retention_choice
    (ε cap θ:ℝ) (m d:ℕ) (hε:0<ε) (hcap:0<cap) (hθ:0<θ)
    (hm:0<m) (hd:1≤d) (hspacing:1/(d:ℝ)≤θ/1024):
    ∃ζglobal ζlocal:ℝ,0<ζglobal ∧ 0<ζlocal ∧
      ζglobal≤θ/4096 ∧ ζlocal≤cap/128 ∧ ζglobal≤ζlocal*ε/2 ∧
      ∃N:ℕ,∀n:ℕ,N≤n→∀q errOrd:ℝ,
        q≤1/((m:ℝ)+1)→errOrd≤θ*n→
        (n:ℝ)*q/d+(((m+1)*d-1:ℕ):ℝ)*(2*((n:ℝ)^(3/4:ℝ)/d)+ζglobal*n)+errOrd≤4*θ*n :=by
  have hdR:0<(d:ℝ):=by exact_mod_cast (show 0<d by omega)
  have hmR:0≤(m:ℝ):=Nat.cast_nonneg _
  have hcut:1/(((m:ℝ)+1)*(d:ℝ))≤θ:=by
    have hm1:1≤(m:ℝ)+1:=by linarith
    have hmdiv:1/(((m:ℝ)+1)*(d:ℝ))≤1/(d:ℝ):=by
      apply one_div_le_one_div_of_le hdR
      nlinarith only [hm1,hdR]
    linarith
  let ζmax:ℝ:=min (θ/4096) (cap*ε/256)
  have hζmax:0<ζmax:=by dsimp [ζmax];positivity
  obtain ⟨ζ,hζ,hζmax',N,hN⟩:=residual_long_error_budget_below m d hm hd θ ζmax hθ hζmax hcut
  let ζlocal:ℝ:=2*ζ/ε
  have hζlocal:0<ζlocal:=by dsimp [ζlocal];positivity
  have hθbudget:ζ≤θ/4096:=hζmax'.trans (min_le_left _ _)
  have hcapbudget:ζ≤cap*ε/256:=hζmax'.trans (min_le_right _ _)
  have hlocal:ζlocal≤cap/128:=by
    dsimp [ζlocal]
    apply (div_le_iff₀ hε).2
    nlinarith only [hcapbudget]
  have hscale:ζ≤ζlocal*ε/2:=by
    dsimp [ζlocal]
    field_simp
    norm_num
  exact ⟨ζ,ζlocal,hζ,hζlocal,hθbudget,hlocal,hscale,N,hN⟩
end Oberwolfach
