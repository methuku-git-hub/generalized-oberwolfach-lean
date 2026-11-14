module

public import Oberwolfach.LongAssignedShortClassZero

@[expose] public section
/-! A positive ordinary seed must belong to a genuine cycle length. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n:ℕ} {U:Type} [Fintype U]

theorem long_assigned_positive_seed_valid_length
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (K m:ℕ) (θ:ℝ) (i:Fin K) (u:U) (c:ℝ)
    (hpos:0<(longAssignedKeptOrdinaryContribution F hF K θ i u/
      longAssignedApproxOrdinaryWeight F hF K m θ u)*c):
    3 ≤ i.val+1 := by
  by_contra h
  have hi:i.val+1<3:=by omega
  have hz:longAssignedKeptOrdinaryContribution F hF K θ i u=0:=
    (long_assigned_kept_below_three_zero F hF K i hi θ u).2
  simp [hz] at hpos
end Oberwolfach
