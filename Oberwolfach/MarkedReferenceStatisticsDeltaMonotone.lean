module

public import Oberwolfach.MarkedReferenceStatistics

@[expose] public section
/-! Weakening a reference tolerance changes neither targets nor domains. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_reference_statistics_delta_mono
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (g:Γ) (j:Color)
    (D ε δ δ' γ p k s t:ℝ) (σ:RawMarkedOutcome V U Γ Color)
    (hδ:δ≤δ') (h:MarkedReferenceStatistics P π d g j D ε δ γ p k s t σ):
    MarkedReferenceStatistics P π d g j D ε δ' γ p k s t σ := by
  refine ⟨h.1,?_,?_⟩
  · intro r hr hr3 b u hu
    exact (h.2.1 r hr hr3 b u hu).trans
      (mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg _))
  · intro b x y hxy
    exact (h.2.2 b x y hxy).trans hδ
end Oberwolfach
