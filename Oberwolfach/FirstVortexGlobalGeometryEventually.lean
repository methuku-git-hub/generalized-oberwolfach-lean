module

public import Oberwolfach.ColourRoundErrorMargins

@[expose] public section
/-! The global required-degree estimate follows from a strict inner-size
gap once the fixed permutation-neighborhood term is negligible. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_global_geometry_eventually
    (d:ℕ) (epsilonInner deltaSmall:ℝ) (hgap:epsilonInner<deltaSmall/4):
    ∃N:ℕ,∀n:ℕ,N≤n→
      epsilonInner*n+((6*d+2:ℕ):ℝ)≤deltaSmall*n/4 :=by
  let gap:=deltaSmall/4-epsilonInner
  have hg:0<gap:=by dsimp [gap];linarith
  obtain ⟨N,hN⟩:=eventually_sublinear_affine_error 0 ((6*d+2:ℕ):ℝ) 1 (2/5) gap
    (by norm_num) (by positivity) (by norm_num) (by norm_num) hg
  refine ⟨N,?_⟩
  intro n hn
  have h:=hN n hn 0 (by positivity)
  dsimp [gap] at h
  nlinarith
end Oberwolfach
