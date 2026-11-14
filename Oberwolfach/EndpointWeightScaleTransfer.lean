module

public import Oberwolfach.EndpointWeightNormalization

@[expose] public section
/-! Transfer positive quadratic weight bounds from the inner row scale to
the ambient physical scale using the original size ratio. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach

theorem endpoint_weight_scale_transfer (a n b B K w:ℝ)
    (ha:0<a) (han:a≤n) (hK:0≤K) (hnK:n≤K*a) (hb:0≤b) (hB:0≤B)
    (hwlo:b/a^2≤w) (hwhi:w≤B/a^2):
    b/n^2≤w ∧ w≤(B*K^2)/n^2:=by
  have hn:0<n:=ha.trans_le han
  have hsq:a^2≤n^2:=pow_le_pow_left₀ ha.le han 2
  have hKsq:n^2≤(K*a)^2:=pow_le_pow_left₀ hn.le hnK 2
  constructor
  · exact (div_le_div_of_nonneg_left hb (by positivity) hsq).trans hwlo
  · apply hwhi.trans
    apply (div_le_div_iff₀ (by positivity : 0<a^2) (by positivity : 0<n^2)).mpr
    have hh:=mul_le_mul_of_nonneg_left hKsq hB
    nlinarith only [hh]
end Oberwolfach
