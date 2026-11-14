module

public import Oberwolfach.ColourRoundErrorMargins

@[expose] public section
/-! The colour-count error and every fixed conflict or absorber term fit
any positive linear error rate for sufficiently large graph order. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_tracked_complement_finite_errors
    (C η:ℝ) (hC:0≤C) (hη:0<η):
    ∃N:ℕ,∀n:ℕ,N≤n→3*(n:ℝ)^(3/5:ℝ)+C≤η*n :=by
  obtain ⟨N,hN⟩:=eventually_sublinear_affine_error 3 C 1 (2/5) η
    (by norm_num) hC (by norm_num) (by norm_num) hη
  refine ⟨N,?_⟩
  intro n hn
  have hpow:(n:ℝ)^(3/5:ℝ)≤1*(n:ℝ)^(1-(2/5:ℝ)):=by norm_num
  exact hN n hn _ hpow
end Oberwolfach
