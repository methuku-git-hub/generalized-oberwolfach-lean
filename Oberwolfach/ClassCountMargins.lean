module

public import Mathlib.Tactic

@[expose] public section

/-! The explicit polynomial margin in a fixed-coordinate counting loss. -/
set_option autoImplicit false
namespace Oberwolfach
 theorem class_count_margin (r:ℕ) (hr:1≤r) (n β K δ L old new:ℝ)
    (hn:0≤n) (hK:0≤K) (hL:L≤δ*n) (hmargin:K*δ≤β/2)
    (hold:β*n^r≤old) (hloss:old-new≤K*L*n^(r-1)):
    β/2*n^r≤new:=by
  have hp:n*n^(r-1)=n^r:=by rw [←pow_succ',Nat.sub_add_cancel hr]
  have h₁:K*L*n^(r-1)≤K*δ*n^r:=by
    calc
      _ ≤ K*(δ*n)*n^(r-1):=mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hL hK) (by positivity)
      _ = _:=by rw [←hp];ring
  have h₂:=mul_le_mul_of_nonneg_right hmargin (pow_nonneg hn r)
  linarith
end Oberwolfach
