module

public import Oberwolfach.LongAssignedPositiveSeedLengths

@[expose] public section
/-! To index all formal classes uniformly, the two nonexistent short
classes may use a dummy triangle length: their seed weights are zero and
the positive-support matching never selects them. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def longAssignedPaddedLength {K:ℕ} (i:Fin K):ℕ:=max 3 (i.val+1)

theorem long_assigned_padded_length_valid {K:ℕ} (i:Fin K):
    3≤longAssignedPaddedLength i := le_max_left _ _

theorem long_assigned_padded_length_true {K:ℕ} (i:Fin K) (hi:3 ≤ i.val+1):
    longAssignedPaddedLength i=i.val+1 := max_eq_right hi

theorem long_assigned_padded_length_upper {K:ℕ} (hK:3≤K) (i:Fin K):
    longAssignedPaddedLength i≤K := by
  apply max_le hK
  exact Nat.succ_le_of_lt i.isLt

theorem long_assigned_positive_seed_padded_length {n K m:ℕ} {U:Type} [Fintype U]
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (θ:ℝ) (i:Fin K) (u:U) (c:ℝ)
    (hpos:0<(longAssignedKeptOrdinaryContribution F hF K θ i u/
      longAssignedApproxOrdinaryWeight F hF K m θ u)*c):
    longAssignedPaddedLength i=i.val+1 := by
  apply long_assigned_padded_length_true
  exact long_assigned_positive_seed_valid_length F hF K m θ i u c hpos
end Oberwolfach
