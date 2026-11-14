module

public import Oberwolfach.MarkedRetainedPairConditional

@[expose] public section
/-! Exact rim relation under the retained-outcome relabelling. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z Γ Color : Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
  [Fintype Γ] [Fintype Color] [Nonempty V] [Nonempty W]
  [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]

theorem marked_retained_rim_restriction
    (F : W ↪o V) (f : W ≃ V) (hf : ∀ w, f w = F w) (g : Z ≃ U)
    (π : Equiv.Perm V) (ρ : Equiv.Perm W) (hc : ∀ w, f (ρ w) = π (f w))
    (P : SimpleGraph V) (d : ℕ) (a : Γ)
    (z : RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a)
    (e : (W×W) ⊕ (W×W)) :
    rawMarkedPairRims (P.comap F) ρ d (markedRetainedPairRestriction f g π ρ hc d a z).1 e ↔
      rawMarkedPairRims P π d z.1 (Sum.map (Prod.map F F) (Prod.map F F) e) := by
  have he : (f : W → V) = F := funext hf
  have hcomm : ∀ w, F (ρ w) = π (F w) := by
    intro w
    simpa only [← he] using hc w
  change rawMarkedPairRims (P.comap F) ρ d (rawMarkedRestrictPair f g z.1) e ↔ _
  rw [he]
  exact rawMarkedRestrictPair_rims F g π ρ hcomm P d z.1 e
end Oberwolfach
