module

public import Oberwolfach.ActualPrescribedLoadLocalOccurrence

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem prescribed_boundary_matching_load_budget
    (A H:ℕ) (d δ a γ n:ℝ)
    (hd:0<d) (hH:(H:ℝ)≤A) (hD:4/d≤δ/8)
    (hN:4*(A:ℝ)^(3/4:ℝ)≤δ*A/8)
    (hMatching:2*(max a γ*n)≤δ*A/4)
    (prescribed bad targets:ℝ)
    (hprescribed:prescribed≤4*H/d+4*(A:ℝ)^(3/4:ℝ)+2*(max a γ*n))
    (hbad:bad≤δ*A/4) (htargets:targets≤δ*A/4):
    prescribed+bad+targets≤δ*A:=by
  have hHd:4*(H:ℝ)/d≤δ*A/8:=by
    have hh:=mul_le_mul_of_nonneg_left hH (show (0:ℝ)≤4/d by positivity)
    have hk:=mul_le_mul_of_nonneg_right hD (show (0:ℝ)≤(A:ℝ) by positivity)
    calc
      4*(H:ℝ)/d = (4/d)*H := by ring
      _ ≤ (4/d)*A := hh
      _ ≤ (δ/8)*A := hk
      _ = δ*A/8 := by ring
  linarith only [hprescribed,hHd,hN,hMatching,hbad,htargets]
end Oberwolfach
