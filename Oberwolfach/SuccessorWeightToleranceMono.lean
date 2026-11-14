module

public import Oberwolfach.SuccessorSequenceWeights

@[expose] public section
/-! Parent and active weights selected at a stricter tolerance remain valid
at either later tolerance, with the same weights. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem successor_sequence_weights_weaken_tolerance
    {V:Type} [Fintype V] {c:ℕ} (G:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (D τ₀ τ A B:ℝ) (w:(Fin c→V)→ℝ) (hD:0≤D) (hτ:τ₀≤τ)
    (h:SuccessorSequenceWeightConditions G π d D τ₀ A B w):
    SuccessorSequenceWeightConditions G π d D τ A B w :=by
  refine ⟨h.nonneg,h.support,h.upper,h.lower,?_,?_⟩
  · intro j x z hclose hadj
    obtain ⟨hl,hu⟩:=h.edges j x z hclose hadj
    exact ⟨by linarith,hu⟩
  · intro j v
    obtain ⟨hl,hu⟩:=h.positions j v
    have hh:=mul_le_mul_of_nonneg_right hτ hD
    exact ⟨by nlinarith,hu⟩
end Oberwolfach
