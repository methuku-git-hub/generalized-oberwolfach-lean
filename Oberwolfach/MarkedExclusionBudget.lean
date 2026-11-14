module

public import Oberwolfach.MarkedHostGreedyChoices

@[expose] public section

/-! Numerical monotonicity for the displayed finite greedy-exclusion budget. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
variable {V:Type} [DecidableEq V]

theorem marked_exclusion_budget_mono (W Z Z':Finset V) (a k b:ℕ) (c:ℝ)
    (hsize:Z'.card+a≤Z.card+k)
    (hbudget:(W.card:ℝ)+(Z.card+k)*(2*b+1)<c):
    (W.card:ℝ)+(Z'.card+a)*(2*b+1)<c:=by
  have hs:(Z'.card:ℝ)+a≤Z.card+k:=by exact_mod_cast hsize
  have hh:=mul_le_mul_of_nonneg_right hs (show 0≤(2*b+1:ℝ) by positivity)
  linarith only [hh,hbudget]

end Oberwolfach
