module

public import Oberwolfach.MarkedRetainedRimRelabel
public import Oberwolfach.MarkedRetainedSpokeRelabel

@[expose] public section
/-! On the same relabelled retained outcome, both rim types and both spoke
types agree with the original marked host. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z Γ Color : Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
  [Fintype Γ] [Fintype Color] [Nonempty V] [Nonempty W]
  [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]

theorem marked_retained_typed_restriction
    (F : W ↪o V) (f : W ≃ V) (hf : ∀ w, f w = F w) (g : Z ≃ U)
    (π : Equiv.Perm V) (ρ : Equiv.Perm W) (hc : ∀ w, f (ρ w) = π (f w))
    (P : SimpleGraph V) (d : ℕ) (a c : Γ) (j : Color)
    (z : RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a) :
    let z' := markedRetainedPairRestriction f g π ρ hc d a z
    (∀ e : (W×W) ⊕ (W×W),
      rawMarkedPairRims (P.comap F) ρ d z'.1 e ↔
      rawMarkedPairRims P π d z.1 (Sum.map (Prod.map F F) (Prod.map F F) e)) ∧
    (∀ (b : Bool) (w : W) (u : Z),
      retainedRawMarkedSpokes ρ d (fun e => z'.1 (Sum.inr e)) a
        (startRetentionMinimum (rawStartHubSet ρ d (fun e => z'.1 (Sum.inr e)) a)) z'.2 c j b w u ↔
      retainedRawMarkedSpokes π d (fun e => z.1 (Sum.inr e)) a
        (startRetentionMinimum (rawStartHubSet π d (fun e => z.1 (Sum.inr e)) a)) z.2 c j b (f w) (g u)) := by
  dsimp only
  constructor
  · intro e
    exact marked_retained_rim_restriction F f hf g π ρ hc P d a z e
  · intro b w u
    exact marked_retained_spoke_restriction f g π ρ hc d a c j z.1 z.2 b w u
end Oberwolfach
