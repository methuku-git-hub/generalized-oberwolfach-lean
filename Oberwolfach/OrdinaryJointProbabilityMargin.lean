module

public import Oberwolfach.GoodPlacementEvents

@[expose] public section
/-! A high-probability preparation event dominates the profile failure bound. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
theorem ordinary_joint_probability_margin (n:ℕ) (hn:4≤n) (p:ℝ)
    (hp:1-1/(n:ℝ)≤p): 2/(n:ℝ)^2<p := by
  have hnR:(4:ℝ)≤n:=by exact_mod_cast hn
  have hnpos:0<(n:ℝ):=by linarith
  have hn2:0<(n:ℝ)^2:=by positivity
  have h:(2:ℝ)/(n:ℝ)^2<1-1/(n:ℝ):=by
    apply (div_lt_iff₀ hn2).2
    have hid:(1-1/(n:ℝ))*(n:ℝ)^2=(n:ℝ)^2-n:=by field_simp <;> ring
    rw [hid]
    nlinarith
  linarith
end Oberwolfach
