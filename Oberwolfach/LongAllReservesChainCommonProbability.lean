module

public import Oberwolfach.LongEveryReserveConcreteClassEvent
public import Oberwolfach.LongEveryClassReserveBoundMonotone
public import Oberwolfach.FiniteLawSupportProbabilityMono

@[expose] public section
/-! Arrange the common, correction and all-reserves events in exactly the
form consumed by the same-sample finite level-chain selector. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable

theorem long_all_reserves_chain_common_probability
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r Dv mm:ℕ) (β ε:ℝ)
    (Q:Vortex U P Dv β ε mm) (Bsmall Bbig:ℕ) (hB:Bsmall≤Bbig)
    (gammaLoss sigmaLoss ξClass Δ:ℝ)
    (θ Dmatch a γ eps βList:ℝ) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (μ:FiniteLaw (MarkedExpandedActualOutcome (U:=U) π d))
    (Other Parent Tail Correction:MarkedExpandedActualOutcome (U:=U) π d→Prop)
    (b:ℝ)
    (hprob:b≤μ.probability (fun z=>Other z ∧ Parent z ∧ Tail z ∧ Correction z ∧
      LongEveryClassValidDeletionEvent Δ P π d r gammaLoss sigmaLoss ξClass z
        (Q.extendedVertices 1) (Q.extendedIndices 1) K Bbig θ Dmatch a γ eps βList F hF weight w ∧
      LongEveryReserveConcreteClassEvent P π d r Dv mm β ε Q Bbig gammaLoss sigmaLoss ξClass Δ z
        θ Dmatch a γ eps βList F hF weight w)):
    b≤μ.probability (fun z=>(Other z ∧
      LongEveryReserveConcreteClassEvent P π d r Dv mm β ε Q Bbig gammaLoss sigmaLoss ξClass Δ z
        θ Dmatch a γ eps βList F hF weight w) ∧ Parent z ∧
      (Tail z ∧ LongEveryClassValidDeletionEvent Δ P π d r gammaLoss sigmaLoss ξClass z
        (Q.extendedVertices 1) (Q.extendedIndices 1) K Bsmall θ Dmatch a γ eps βList F hF weight w) ∧ Correction z) :=by
  apply hprob.trans
  apply finiteLaw_probability_mono
  intro z hz
  exact ⟨⟨hz.1,hz.2.2.2.2.2⟩,hz.2.1,⟨hz.2.2.1,
    long_every_class_valid_deletion_reserve_bound_mono Δ P π d r gammaLoss sigmaLoss ξClass z
      (Q.extendedVertices 1) (Q.extendedIndices 1) K Bsmall Bbig hB θ Dmatch a γ eps βList F hF weight w hz.2.2.2.2.1⟩,hz.2.2.2.1⟩
end Oberwolfach
