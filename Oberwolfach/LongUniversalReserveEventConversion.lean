module

public import Oberwolfach.LongCorrectionReserveUniversalEvent
public import Oberwolfach.LongCorrectionUniversalMatchingReserveEvent

@[expose] public section
/-! The two checked interfaces retain the same correction, terminal reserve
and every-class matching, including the same forbidden resource set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable

theorem long_universal_reserve_event_to_matching_event
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r Dv mm:ℕ) (β ε:ℝ)
    (Q:Vortex U P Dv β ε mm) (L a₀ b₀ e₀:ℕ) (gammaLoss sigmaLoss extra ξClass Δ:ℝ)
    (z:MarkedExpandedActualOutcome (U:=U) π d) (θ a γ eps βList:ℝ)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ) (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (F₀:Finset (Finset (Fin n)⊕(Fin n×U)))
    (h:LongCorrectionReserveUniversalEvent P π d r Dv mm β ε Q L a₀ b₀ e₀
      gammaLoss sigmaLoss extra ξClass Δ z θ a γ eps βList F hF weight w F₀):
    LongCorrectionUniversalMatchingReserveEvent P π d r Dv mm β ε Q L a₀ b₀ e₀
      gammaLoss sigmaLoss extra ξClass Δ z θ a γ eps βList F hF weight w F₀ :=by
  unfold LongCorrectionReserveUniversalEvent at h
  unfold LongCorrectionUniversalMatchingReserveEvent
  exact h
end Oberwolfach
