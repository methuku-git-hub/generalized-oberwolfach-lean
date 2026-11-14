module

public import Oberwolfach.LongRequiredDegreePreciseFromRows

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_required_degree_numeric_margin
    (N I d:ℕ) (θ lam t δ:ℝ) (hθ:0≤θ) (hI:(I:ℝ)≤N)
    (hθsmall:θ≤δ/32) (hlam:lam≤δ/16)
    (ht:t≤δ*N/16) (hd:((6*d+2:ℕ):ℝ)≤δ*N/16):
    2*θ*I+t+lam*N+(6*d+2:ℕ)≤δ*N/4:=by
  have hN:(0:ℝ)≤N:=Nat.cast_nonneg N
  have hi:=mul_le_mul_of_nonneg_left hI (show 0≤2*θ by positivity)
  have hhθ:=mul_le_mul_of_nonneg_right hθsmall hN
  have hhlam:=mul_le_mul_of_nonneg_right hlam hN
  nlinarith only [hi,hhθ,hhlam,ht,hd]
end Oberwolfach
