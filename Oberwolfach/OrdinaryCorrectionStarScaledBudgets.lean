module

public import Oberwolfach.OrdinaryConstructedCorrectionTriangleCoverOuter

@[expose] public section
/-! Concrete hierarchy estimates for the correction-star incidence and
    total-cardinality budgets, including the integer ceiling. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_correction_star_scaled_budgets (n u i:ℕ) (κ ξ:ℝ)
    (hκ:0<κ) (hκ1:κ≤1) (hξ:0<ξ) (hξsmall:80*ξ≤κ^2)
    (hu:u≤n) (hi:i≤n) (hn:4≤κ^2*n):
    (⌈10*ξ*i⌉₊:ℝ)≤κ*n ∧
      (((n+u)*⌈10*ξ*i⌉₊:ℕ):ℝ)≤κ^2*(n:ℝ)^2:=by
  have hn0:(0:ℝ)≤n:=Nat.cast_nonneg _
  have hu0:(0:ℝ)≤u:=Nat.cast_nonneg _
  have hi0:(0:ℝ)≤ i:=Nat.cast_nonneg _
  have hi':(i:ℝ)≤n:=by exact_mod_cast hi
  have hu':(u:ℝ)≤n:=by exact_mod_cast hu
  have hprod:10*ξ*i≤κ^2*n/8:=by
    have ha:=mul_nonneg (show (0:ℝ)≤ξ by positivity) (sub_nonneg.mpr hi')
    have hb:=mul_nonneg (sub_nonneg.mpr hξsmall) hn0
    nlinarith
  have hceil:(⌈10*ξ*i⌉₊:ℝ)≤10*ξ*i+1:=
    (Nat.ceil_lt_add_one (by positivity:0≤10*ξ*i)).le
  have hhalf:(⌈10*ξ*i⌉₊:ℝ)≤κ^2*n/2:=by nlinarith
  have hκsq:κ^2≤κ:=by nlinarith
  have hκn:=mul_le_mul_of_nonneg_right hκsq hn0
  have hfirst:(⌈10*ξ*i⌉₊:ℝ)≤κ*n:=by nlinarith
  refine ⟨hfirst,?_⟩
  have hc0:(0:ℝ)≤⌈10*ξ*i⌉₊:=Nat.cast_nonneg _
  have hsize:(n:ℝ)+u≤2*n:=by linarith
  have ha:=mul_le_mul_of_nonneg_right hsize hc0
  have hb:=mul_le_mul_of_nonneg_left hhalf (show (0:ℝ)≤2*n by positivity)
  have he:((n:ℝ)+u)*(⌈10*ξ*i⌉₊:ℝ)≤κ^2*(n:ℝ)^2:=by nlinarith
  exact_mod_cast he
end Oberwolfach
