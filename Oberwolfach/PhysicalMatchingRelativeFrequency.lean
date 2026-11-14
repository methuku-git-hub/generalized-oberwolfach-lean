module

public import Oberwolfach.PhysicalMatchingFrequencyDeviation

@[expose] public section
/-! Relative test-mass accuracy transfers to relative frequency accuracy
for the matched candidates. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach

theorem physical_matching_relative_frequency
    (r mass count f n θ ε γ:ℝ) (hr:0≤r) (hγ:0≤γ)
    (hdev:|r*mass-(1-θ)*f*n|≤ε*f*n)
    (hlo:(1-γ)*mass≤count) (hhi:count≤(1+γ)*mass):
    |r*count-(1-θ)*f*n|≤(ε+γ*(1-θ+ε))*f*n :=by
  have hh:=physical_matching_frequency_deviation r mass count ((1-θ)*f*n) (ε*f*n) γ hr hγ hdev hlo hhi
  convert hh using 1 <;> ring
end Oberwolfach
