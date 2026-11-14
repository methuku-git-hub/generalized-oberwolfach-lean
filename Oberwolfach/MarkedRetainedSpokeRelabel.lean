module

public import Oberwolfach.MarkedRetainedStartRestriction
public import Oberwolfach.RetainedIntervalStateRelabel
public import Oberwolfach.RetainedMarkedSpokeChanges

@[expose] public section
/-! Exact agreement of both types of retained spoke under relabelling. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z Γ Color : Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
  [Fintype Γ] [Fintype Color] [Nonempty V] [Nonempty W]
  [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]

theorem marked_retained_state_restriction
    (f : W ≃ V) (g : Z ≃ U) (π : Equiv.Perm V) (ρ : Equiv.Perm W)
    (hc : ∀ x, f (ρ x) = π (f x)) (d : ℕ) (a : Γ)
    (σ : RawMarkedOutcome V U Γ Color)
    (J : StartRetentionOutcome (rawStartHubSet π d (fun e => σ (Sum.inr e)) a)
      (startRetentionMinimum (rawStartHubSet π d (fun e => σ (Sum.inr e)) a)))
    (w : W) (z : Z) :
    let A := rawStartHubSet π d (fun e => σ (Sum.inr e)) a
    let B := rawStartHubSet ρ d (fun e => (rawMarkedRestrictPair f g σ) (Sum.inr e)) a
    retainedRawFamilyState ρ d (fun e => (rawMarkedRestrictPair f g σ) (Sum.inr e)) a
      (startRetentionMinimum B) (markedRetainedPairSecond f g π ρ hc d a σ J) (w,z) =
    retainedRawFamilyState π d (fun e => σ (Sum.inr e)) a (startRetentionMinimum A) J (f w,g z) := by
  dsimp only [retainedRawFamilyState]
  have hs : (fun e => (rawMarkedRestrictPair f g σ) (Sum.inr (z,e))) =
      rawIntervalRestrictVertices f (fun e => σ (Sum.inr (g z,e))) := by
    funext e
    cases e with
    | inl e => rfl
    | inr e => cases e <;> rfl
  rw [hs]
  apply retained_interval_state_relabel f π ρ hc
  intro x c
  exact marked_retained_start_restriction f g π ρ hc d a σ J x z c

theorem marked_retained_spoke_restriction
    (f : W ≃ V) (g : Z ≃ U) (π : Equiv.Perm V) (ρ : Equiv.Perm W)
    (hc : ∀ x, f (ρ x) = π (f x)) (d : ℕ) (a c : Γ) (j : Color)
    (σ : RawMarkedOutcome V U Γ Color)
    (J : StartRetentionOutcome (rawStartHubSet π d (fun e => σ (Sum.inr e)) a)
      (startRetentionMinimum (rawStartHubSet π d (fun e => σ (Sum.inr e)) a)))
    (b : Bool) (w : W) (z : Z) :
    let A := rawStartHubSet π d (fun e => σ (Sum.inr e)) a
    let B := rawStartHubSet ρ d (fun e => (rawMarkedRestrictPair f g σ) (Sum.inr e)) a
    retainedRawMarkedSpokes ρ d (fun e => (rawMarkedRestrictPair f g σ) (Sum.inr e)) a
      (startRetentionMinimum B) (markedRetainedPairSecond f g π ρ hc d a σ J) c j b w z ↔
    retainedRawMarkedSpokes π d (fun e => σ (Sum.inr e)) a (startRetentionMinimum A) J c j b (f w) (g z) := by
  have hh := marked_retained_state_restriction f g π ρ hc d a σ J w z
  cases b <;> simp only [retainedRawMarkedSpokes] <;> rw [hh]
end Oberwolfach
