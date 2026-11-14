module

public import Oberwolfach.LongEveryClassValidDeletionEvent

@[expose] public section
/-! A matching test valid for a larger reserve budget applies to a smaller
terminal reserve budget without changing its sample or deletion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable

theorem long_every_class_valid_deletion_reserve_bound_mono
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (Δ:ℝ) (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r:ℕ)
    (γLoss σLoss ξClass:ℝ) (z:MarkedExpandedActualOutcome (U:=U) π d)
    (T:Finset (Fin n)) (W:Finset U) (K Bsmall Bbig:ℕ) (hB:Bsmall≤Bbig)
    (θ D alpha γ eps βList:ℝ)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (h:LongEveryClassValidDeletionEvent Δ P π d r γLoss σLoss ξClass z T W K Bbig θ D alpha γ eps βList F hF weight w):
    LongEveryClassValidDeletionEvent Δ P π d r γLoss σLoss ξClass z T W K Bsmall θ D alpha γ eps βList F hF weight w :=by
  dsimp only [LongEveryClassValidDeletionEvent] at h ⊢
  intro D₀ hvalid C hcard hdis
  exact h D₀ hvalid C (hcard.trans hB) hdis
end Oberwolfach
