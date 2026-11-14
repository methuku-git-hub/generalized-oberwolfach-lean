module

public import Oberwolfach.MixedMatchedHubDeviation

@[expose] public section
/-! A matching that approximates a hub test inherits its target frequency
with an explicit absolute error, without changing candidate weights. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach

theorem physical_matching_frequency_deviation
    (r mass count target err γ:ℝ) (hr:0≤r) (hγ:0≤γ)
    (hdev:|r*mass-target|≤err)
    (hlo:(1-γ)*mass≤count) (hhi:count≤(1+γ)*mass):
    |r*count-target|≤err+γ*(target+err) :=by
  have hd:=abs_le.mp hdev
  have hlow:=mul_le_mul_of_nonneg_left hlo hr
  have hhigh:=mul_le_mul_of_nonneg_left hhi hr
  have hγmass:=mul_le_mul_of_nonneg_left hd.2 hγ
  apply abs_le.mpr
  constructor <;> nlinarith
end Oberwolfach
