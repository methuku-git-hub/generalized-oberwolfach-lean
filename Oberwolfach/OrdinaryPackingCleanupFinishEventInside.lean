module

public import Oberwolfach.OrdinaryPackingCleanupFinishEvent
public import Oberwolfach.OrdinaryTriangleFinishSampleInputsInside
public import Oberwolfach.OrdinaryTriangleFinishSampleInputs

@[expose] public section
/-! Add the triangle finish to a packing-and-cleanup event on the same
outcome, without altering its probability bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
set_option synthInstance.maxSize 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_packing_cleanup_outcome_has_finish_inside
    (Q₀ Q F:SimpleGraph V) (H₀ H:V→U→Prop) (X:Finset V) (Z:Finset U)
    (σ:Sym2 (V⊕U)→Bool) (γ κ b B ε η ζ p εs τ ν:ℝ)
    (i:OrdinaryTriangleFinishSampleInputsInside Q₀ Q F H₀ H X Z σ γ κ b B ε η ζ p εs τ ν)
    (h:OrdinaryPackingCleanupOutcome Q₀ F H₀ X Z σ τ ν):
    OrdinaryPackingCleanupFinishOutcome Q₀ F H₀ X Z σ p τ ν:=by
  obtain ⟨M,⟨K⟩⟩:=h
  exact ⟨M,K,ordinary_triangle_finish_from_inside_sample_inputs Q₀ Q F H₀ H X Z σ γ κ b B ε η ζ p εs τ ν i M K⟩

theorem ordinary_packing_cleanup_finish_event_inside {Ω:Type} [Fintype Ω]
    (μ:FiniteLaw Ω) (E:Ω→Prop) (e:ℝ)
    (Q₀ Q F:Ω→SimpleGraph V) (H₀ H:Ω→V→U→Prop) (X:Ω→Finset V) (Z:Ω→Finset U)
    (σ:Ω→Sym2 (V⊕U)→Bool) (γ κ b B ε η ζ p εs τ ν:ℝ)
    (hprob:1-e≤μ.probability (fun a=>E a ∧ OrdinaryPackingCleanupOutcome (Q₀ a) (F a) (H₀ a) (X a) (Z a) (σ a) τ ν))
    (hinput:∀a,E a→OrdinaryTriangleFinishSampleInputsInside (Q₀ a) (Q a) (F a) (H₀ a) (H a) (X a) (Z a) (σ a)
      γ κ b B ε η ζ p εs τ ν):
    1-e≤μ.probability (fun a=>E a ∧ OrdinaryPackingCleanupFinishOutcome (Q₀ a) (F a) (H₀ a) (X a) (Z a) (σ a) p τ ν):=by
  apply hprob.trans
  apply finiteLaw_probability_mono
  intro a ha
  exact ⟨ha.1,ordinary_packing_cleanup_outcome_has_finish_inside (Q₀ a) (Q a) (F a) (H₀ a) (H a)
    (X a) (Z a) (σ a) γ κ b B ε η ζ p εs τ ν (hinput a ha.1) ha.2⟩
end Oberwolfach
