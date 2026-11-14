module

public import Oberwolfach.ColourRoundErrorMargins

@[expose] public section
/-! The all-hub boundary count has an arbitrarily small linear rate once
the spacing is fixed sufficiently large and the host is large. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_all_hub_boundary_eventually (d:ℕ) (b:ℝ)
    (hd:0<d) (hb:0<b) (hspacing:4/(d:ℝ)<b):
    ∃N:ℕ,∀n:ℕ,N≤n→∀u:ℕ,u≤n→
      4*(u:ℝ)/d+4*(n:ℝ)^(3/4:ℝ)≤b*n :=by
  let gap:=b-4/(d:ℝ)
  have hgap:0<gap:=by dsimp [gap];linarith
  have hdp:0<(d:ℝ):=by exact_mod_cast hd
  obtain ⟨N,hN⟩:=eventually_sublinear_affine_error 4 0 1 (1/4) gap
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hgap
  refine ⟨N,?_⟩
  intro n hn u hu
  have herr:=hN n hn ((n:ℝ)^(3/4:ℝ)) (by norm_num)
  have hu':(u:ℝ)≤n:=by exact_mod_cast hu
  have hpart:4*(u:ℝ)/d≤(4/(d:ℝ))*n:=by
    have heq:4*(u:ℝ)/d=(4/(d:ℝ))*u:=by ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left hu' (by positivity)
  dsimp [gap] at herr
  nlinarith
end Oberwolfach
