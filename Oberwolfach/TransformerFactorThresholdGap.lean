module

public import Oberwolfach.ThresholdComparisons

@[expose] public section

/-! The odd-cycle decomposition threshold can be strictly above the
minimum-degree coefficient used by the transformer factor theorem. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach

theorem odd_transformer_factor_threshold_gap (r:ℕ) (hr:5≤r) (hodd:Odd r) :
    transformerDensity r + 1/(2*(r:ℝ)*((r:ℝ)-1)) ≤ cycleThreshold r := by
  have hrR : (5:ℝ)≤r := by exact_mod_cast hr
  have hr0 : (r:ℝ)≠0 := by linarith
  have hr1 : (r:ℝ)-1≠0 := by linarith
  have hr2 : (2:ℝ)*r-2≠0 := by linarith
  have hident : (r:ℝ)/(2*r-2)=1/2+1/(2*r)+1/(2*r*(r-1)) := by
    field_simp
    ring
  have hlow:=cycleThreshold_odd_sharp_lower (show 3≤r by omega) hodd
  rw [hident] at hlow
  have hne3 : r≠3 := by omega
  have hne4 : r≠4 := by omega
  have hnEven : ¬Even r := Nat.not_even_iff_odd.mpr hodd
  simpa only [transformerDensity,cycleFactorDensity,hne3,hne4,hnEven,ite_false] using hlow

end Oberwolfach
