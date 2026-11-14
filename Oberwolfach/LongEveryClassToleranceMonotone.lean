module

public import Oberwolfach.LongEveryClassValidDeletionEvent

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable

theorem long_every_class_matching_result_tolerance_mono
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (Δ:ℝ) (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r:ℕ)
    (γLoss σLoss ξold ξnew:ℝ) (hξ:ξnew≤ξold) (z:MarkedExpandedActualOutcome (U:=U) π d)
    (T:Finset (Fin n)) (K:ℕ) (θ D alpha γ eps βList:ℝ)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (D₀:MarkedReferenceDeletion P π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
    (C:Finset (Finset (Fin n)⊕(Fin n×U)))
    (h:LongEveryClassMatchingResult Δ P π d r γLoss σLoss ξold z T K θ D alpha γ eps βList F hF weight w D₀ C):
    LongEveryClassMatchingResult Δ P π d r γLoss σLoss ξnew z T K θ D alpha γ eps βList F hF weight w D₀ C := by
  dsimp only [LongEveryClassMatchingResult] at h ⊢
  intro S hS hreg hedit hagree hA
  exact h S hS hreg (fun v=>(hedit v).trans (mul_le_mul_of_nonneg_right hξ (Nat.cast_nonneg n))) hagree hA

theorem long_every_class_valid_deletion_tolerance_mono
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (Δ:ℝ) (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r:ℕ)
    (γLoss σLoss ξold ξnew:ℝ) (hξ:ξnew≤ξold) (z:MarkedExpandedActualOutcome (U:=U) π d)
    (T:Finset (Fin n)) (W:Finset U) (K B:ℕ) (θ D alpha γ eps βList:ℝ)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (h:LongEveryClassValidDeletionEvent Δ P π d r γLoss σLoss ξold z T W K B θ D alpha γ eps βList F hF weight w):
    LongEveryClassValidDeletionEvent Δ P π d r γLoss σLoss ξnew z T W K B θ D alpha γ eps βList F hF weight w := by
  dsimp only [LongEveryClassValidDeletionEvent] at h ⊢
  intro D₀ hvalid C hcard hdis
  exact long_every_class_matching_result_tolerance_mono Δ P π d r γLoss σLoss ξold ξnew hξ z T K θ D alpha γ eps βList F hF weight w D₀ C.edges (h D₀ hvalid C hcard hdis)
end Oberwolfach
