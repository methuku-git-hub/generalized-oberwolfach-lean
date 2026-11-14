module

public import Oberwolfach.OrdinaryCycleSamplingScales

@[expose] public section
/-! Scalar margins for a nearly regular set of expected sampled degrees. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach

theorem cycle_sampling_degree_margins
    (θ T D m:ℝ) (hθ:0≤θ) (hθhi:θ≤1/10) (hT:0≤T)
    (hmlo:(1-θ/2)*T≤m) (hmhi:m≤(1+θ/2)*T)
    (hDlo:(1+2*θ)*T≤D) (hDhi:D≤(1+3*θ)*T):
    (1-10*θ)*D≤(1-θ)*m ∧ (1+θ)*m≤D := by
  have hc1:0≤1-10*θ:=by linarith
  have hc2:0≤1-θ:=by linarith
  have hc3:0≤1+θ:=by linarith
  have hlo: (1-10*θ)*(1+3*θ)≤(1-θ)*(1-θ/2):=by nlinarith [sq_nonneg θ]
  have hhi: (1+θ)*(1+θ/2)≤1+2*θ:=by nlinarith [sq_nonneg θ]
  have h1:=mul_le_mul_of_nonneg_left hDhi hc1
  have h2:=mul_le_mul_of_nonneg_right hlo hT
  have h3:=mul_le_mul_of_nonneg_left hmlo hc2
  have h4:=mul_le_mul_of_nonneg_left hmhi hc3
  have h5:=mul_le_mul_of_nonneg_right hhi hT
  constructor <;> nlinarith only [h1,h2,h3,h4,h5,hDlo]
end Oberwolfach
