module

public import Oberwolfach.ReservedSpokeIndependentMargins

@[expose] public section
/-! Reserve a fixed fraction of the ordinary-label margin for each deletion. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem reserved_list_trim_budget
    (β ε η ζ:ℝ) (m:ℕ) (hβ:0≤β)
    (hε:ε≤β/4) (hη:η≤β/4) (hζ:ζ≤β/4)
    (hm:1/(100*(m:ℝ))≤β/4):
    2*β+2*ζ≤4*β ∧ β+ε+1/(100*(m:ℝ))+η≤2*β:=by
  constructor <;> linarith
end Oberwolfach
