module

public import Oberwolfach.OrdinaryJointProbabilityMargin

@[expose] public section
/-! Polynomially high-probability events meet the additional-event margin. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
theorem ordinary_extra_event_probability_margin (n:ℕ) (hn:4≤n) (p:ℝ)
    (hp:1-1/(n:ℝ)≤p): 1/(n:ℝ)+2/(n:ℝ)^2<p := by
  have hnR:(4:ℝ)≤n:=by exact_mod_cast hn
  have hnpos:0<(n:ℝ):=by linarith
  have hn2:0<(n:ℝ)^2:=by positivity
  have h:(1:ℝ)/(n:ℝ)+2/(n:ℝ)^2<1-1/(n:ℝ):=by
    have hid1:(1/(n:ℝ))*(n:ℝ)^2=(n:ℝ):=by field_simp <;> ring
    have hid2:(2/(n:ℝ)^2)*(n:ℝ)^2=2:=by field_simp
    have hid3:(1-1/(n:ℝ))*(n:ℝ)^2=(n:ℝ)^2-n:=by field_simp <;> ring
    have hnum:((1/(n:ℝ)+2/(n:ℝ)^2)*(n:ℝ)^2)<(1-1/(n:ℝ))*(n:ℝ)^2:=by
      rw [add_mul,hid1,hid2,hid3]
      nlinarith
    nlinarith only [hnum,hn2]
  linarith
end Oberwolfach
