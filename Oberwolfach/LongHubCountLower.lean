module

public import Mathlib.Tactic

@[expose] public section
/-! Convert an absolute raw spoke-count error into the lower count needed
for a retained hub test, without changing its sampling marginal. -/
set_option autoImplicit false
namespace Oberwolfach

theorem long_hub_count_lower (card b n error:ℝ)
    (h:|card-b*n|≤error) (hsmall:error≤b*n/2):
    b*n/2≤card:=by
  have hh:=(abs_le.mp h).1
  linarith
end Oberwolfach
