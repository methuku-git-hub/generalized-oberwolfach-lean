module

public import Oberwolfach.LongSelectedListMargins

@[expose] public section
/-! The auxiliary spacing and order needed for protected-pair labels can be
chosen after the original positive parameters. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach

theorem long_protected_pair_margins (θ ρ₀:ℝ) (hθ:0<θ) (hρ₀:0<ρ₀):
    ∃dMin:ℕ,∀d:ℕ,dMin≤d→
      1/(8*(d:ℝ))≤θ/2 ∧ 1/(4*(d:ℝ))≤(5/64:ℝ)*θ^2 ∧
      ∃N:ℕ,∀n:ℕ,N≤n→5*(n:ℝ)^(3/4:ℝ)≤(5*θ^2*ρ₀/1024)*n:=by
  obtain ⟨D,hD⟩:=exists_nat_gt (max (1/(4*θ)) (16/(5*θ^2)))
  refine ⟨max D 2,?_⟩
  intro d hd
  have hd0:0<(d:ℝ):=by exact_mod_cast (show 0<d by omega)
  have hbound:max (1/(4*θ)) (16/(5*θ^2))≤(d:ℝ):=
    le_of_lt (lt_of_lt_of_le hD (by exact_mod_cast (show D≤d by omega)))
  have h1:1/(4*θ)≤(d:ℝ):=le_trans (le_max_left _ _) hbound
  have h2:16/(5*θ^2)≤(d:ℝ):=le_trans (le_max_right _ _) hbound
  have hspace1:1/(8*(d:ℝ))≤θ/2:=by
    have hh:1≤(d:ℝ)*(4*θ):=(div_le_iff₀ (by positivity:0<4*θ)).1 h1
    apply (div_le_iff₀ (by positivity:0<8*(d:ℝ))).2
    nlinarith
  have hspace2:1/(4*(d:ℝ))≤(5/64:ℝ)*θ^2:=by
    have hh:16≤(d:ℝ)*(5*θ^2):=(div_le_iff₀ (by positivity:0<5*θ^2)).1 h2
    apply (div_le_iff₀ (by positivity:0<4*(d:ℝ))).2
    nlinarith
  refine ⟨hspace1,hspace2,?_⟩
  obtain ⟨N,hN⟩:=eventually_three_quarters_and_constant_le_linear (θ^2*ρ₀/1024) 0 (by positivity)
  refine ⟨N,?_⟩
  intro n hn
  have hh:=hN n hn
  nlinarith
end Oberwolfach
