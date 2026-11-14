module

public import Oberwolfach.EndpointWeightNormalization

@[expose] public section
/-! The original additive rim-spoke balance bound implies the normalized
endpoint balance whenever the positive denominator absorbs the error. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach

theorem endpoint_balance_from_difference (x y e δ:ℝ) (hy:0<y)
    (h:|x-y|≤e) (hm:e≤δ*y):|x/y-1|≤δ:=by
  have he:x/y-1=(x-y)/y:=by field_simp
  rw [he,abs_div,abs_of_pos hy]
  exact (div_le_iff₀ hy).2 (h.trans hm)
end Oberwolfach
