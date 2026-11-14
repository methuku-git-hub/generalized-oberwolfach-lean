module

public import Oberwolfach.LongCorrectionReserveConcreteClassStepEvent
public import Oberwolfach.FiniteLawSupportProbabilityMono

@[expose] public section
/-! Attach independently chosen level budgets to the actual correction,
matching and terminal reserve without any additional probability loss. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 40000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable

theorem long_correction_reserve_step_probability
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r Dv mm:ℕ) (β ε:ℝ)
    (Q:Vortex U P Dv β ε mm) (L a₀ b₀ e₀:ℕ)
    (gammaLoss sigmaLoss extra gammaStep sigmaStep ξClass Δ:ℝ)
    (hγ:gammaLoss+extra≤gammaStep) (hσ:sigmaLoss+extra≤sigmaStep)
    (θ a γ eps βList:ℝ) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (F₀:Finset (Finset (Fin n)⊕(Fin n×U)))
    (μ:FiniteLaw (MarkedExpandedActualOutcome (U:=U) π d))
    (Prior:MarkedExpandedActualOutcome (U:=U) π d→Prop) (b:ℝ):
    b≤μ.probability (fun z=>Prior z ∧ LongCorrectionReserveConcreteClassEvent P π d r Dv mm β ε Q L a₀ b₀ e₀
      gammaLoss sigmaLoss extra ξClass Δ z θ a γ eps βList F hF weight w F₀)→
    b≤μ.probability (fun z=>Prior z ∧ LongCorrectionReserveConcreteClassEvent P π d r Dv mm β ε Q L a₀ b₀ e₀
      gammaLoss sigmaLoss extra ξClass Δ z θ a γ eps βList F hF weight w F₀ ∧
      LongCorrectionReserveConcreteClassStepEvent P π d r Dv mm β ε Q L a₀ b₀ e₀
      gammaLoss sigmaLoss extra gammaStep sigmaStep ξClass Δ z θ a γ eps βList F hF weight w F₀):=by
  intro hp
  apply hp.trans
  apply finiteLaw_probability_mono
  intro z hz
  exact ⟨hz.1,hz.2,long_correction_reserve_concrete_class_step_event P π d r Dv mm β ε Q L a₀ b₀ e₀
    gammaLoss sigmaLoss extra gammaStep sigmaStep ξClass Δ hγ hσ z θ a γ eps βList F hF weight w F₀ hz.2⟩
end Oberwolfach
