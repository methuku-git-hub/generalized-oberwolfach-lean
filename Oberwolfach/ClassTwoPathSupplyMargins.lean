module

public import Oberwolfach.ColourRoundErrorMargins

@[expose] public section
/-! The common selected two-path test has a sublinear error and a fixed
spacing loss. Both fit the routing supply after the edit rate is chosen. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem eventually_class_two_path_supply (β:ℝ) (hβ:0<β) (d:ℕ):
    ∃N:ℕ,∀n:ℕ,N≤n→∀ξ:ℝ,ξ≤β/4→
      (n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)+2*(ξ*n)≤β*n:=by
  let C:ℝ:=2*(2*((3*d:ℕ):ℝ)+1)
  obtain ⟨N,hN⟩:=eventually_sublinear_affine_error 1 C 1 (1/4) (β/2)
    (by norm_num) (by dsimp [C];positivity) (by norm_num) (by norm_num) (by positivity)
  refine ⟨N,?_⟩
  intro n hn ξ hξ
  have hs:=hN n hn ((n:ℝ)^(3/4:ℝ)) (by norm_num)
  have hξn:=mul_le_mul_of_nonneg_right hξ (show 0≤(n:ℝ) by positivity)
  dsimp [C] at hs
  nlinarith
end Oberwolfach
