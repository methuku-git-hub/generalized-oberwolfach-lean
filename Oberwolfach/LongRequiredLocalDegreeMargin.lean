module

public import Oberwolfach.LongRequiredDegreeMargin

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_required_local_degree_numeric_margin
    (N I d:ℕ) (θ lam t δ:ℝ) (hθ:θ≤δ/32)
    (ht:t≤δ*I/16) (hlam:lam*N≤δ*I/16)
    (hd:((6*d+2:ℕ):ℝ)≤δ*I/16):
    2*θ*I+t+lam*N+(6*d+2:ℕ)≤δ*I/4:=by
  have hI:(0:ℝ)≤I:=Nat.cast_nonneg I
  have hh:=mul_le_mul_of_nonneg_right hθ hI
  nlinarith only [hh,ht,hlam,hd]
end Oberwolfach
