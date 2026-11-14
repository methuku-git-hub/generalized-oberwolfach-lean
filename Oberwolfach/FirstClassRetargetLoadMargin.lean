module

public import Mathlib.Tactic

@[expose] public section
/-! The first vortex's inner-set size converts the ordered edit tolerance
into the local load margin used for retargeting the source. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_class_retarget_load_margin
    (n A:ℕ) (ε ξ δold δnew:ℝ) (hgap:0≤δnew-δold)
    (hsize:ε*(n:ℝ)/2≤A) (hξ:ξ≤(δnew-δold)*ε/2):
    ξ*n≤(δnew-δold)*(A:ℝ):=by
  have hn:0≤(n:ℝ):=Nat.cast_nonneg n
  have h1:=mul_le_mul_of_nonneg_right hξ hn
  have h2:=mul_le_mul_of_nonneg_left hsize hgap
  nlinarith
end Oberwolfach
