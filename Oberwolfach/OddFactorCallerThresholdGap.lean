module

public import Oberwolfach.ThresholdComparisons

@[expose] public section
/-! For odd cycle lengths the manuscript's factor density is strictly below
the ordinary cycle-decomposition threshold. A small positive caller margin
does not by itself satisfy an above-threshold factor theorem. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem odd_factor_caller_below_cycle_threshold
    {r:ℕ} (hr:3≤r) (hodd:Odd r) (β:ℝ)
    (hβ:β < 2/((r:ℝ)*(r-1))):
    cycleFactorDensity r+β/4<cycleThreshold r:=by
  have hre:(3:ℝ)≤r:=by exact_mod_cast hr
  have hne:¬Even r:=Nat.not_even_iff_odd.mpr hodd
  have h4:r≠4:=by
    intro h; subst r; norm_num at hodd
  have hlo:=cycleThreshold_ge_ordinaryCycleLowerDensity hr
  simp only [ordinaryCycleLowerDensity,h4,hne,ite_false] at hlo
  have hd1:(2*(r:ℝ)-2)≠0:=by linarith
  have hd2:(r:ℝ)≠0:=by linarith
  have hd3:(r:ℝ)-1≠0:=by linarith
  have hid:(1/(2*(r:ℝ)-2):ℝ)=1/(2*r)+1/(2*r*(r-1)):=by
    field_simp
    <;> ring
  have hid2:(2/((r:ℝ)*(r-1)))/4=1/(2*r*(r-1)):=by
    field_simp
    <;> ring
  simp only [cycleFactorDensity,hne,ite_false]
  linarith
end Oberwolfach
