module

public import Oberwolfach.MarkedConditionalRetentionLaw
public import Oberwolfach.RawMarkedRetention
public import Oberwolfach.FiniteLawEquivInverse
public import Oberwolfach.FiniteSigmaTransport

@[expose] public section
/-! Relabel both stages of the marked experiment using the actual eligible
sets and the actual common retention minimum. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z Γ Color : Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
  [Fintype Γ] [Fintype Color] [Nonempty V] [Nonempty W]
  [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]

def markedRetainedPairSecond (f : W ≃ V) (g : Z ≃ U)
    (π : Equiv.Perm V) (ρ : Equiv.Perm W) (hc : ∀ x, f (ρ x) = π (f x))
    (d : ℕ) (a : Γ) (σ : RawMarkedOutcome V U Γ Color)
    (J : StartRetentionOutcome (rawStartHubSet π d (fun e => σ (Sum.inr e)) a)
      (startRetentionMinimum (rawStartHubSet π d (fun e => σ (Sum.inr e)) a))) :
    StartRetentionOutcome (rawStartHubSet ρ d (fun e => (rawMarkedRestrictPair f g σ) (Sum.inr e)) a)
      (startRetentionMinimum (rawStartHubSet ρ d (fun e => (rawMarkedRestrictPair f g σ) (Sum.inr e)) a)) := by
  let A := rawStartHubSet π d (fun e => σ (Sum.inr e)) a
  let B := rawStartHubSet ρ d (fun e => (rawMarkedRestrictPair f g σ) (Sum.inr e)) a
  let t := startRetentionMinimum A
  have he : startRetentionMinimum B = t := raw_marked_retention_minimum_relabel f g π ρ hc d σ a
  have hm : ∀ w x, x ∈ B w ↔ g x ∈ A (f w) := raw_marked_start_hub_mem_relabel f g π ρ hc d σ a
  change StartRetentionOutcome B (startRetentionMinimum B)
  exact he.symm ▸ (startRetentionRelabelEquiv f g A B hm t).symm J

def markedRetainedPairRestriction (f : W ≃ V) (g : Z ≃ U)
    (π : Equiv.Perm V) (ρ : Equiv.Perm W) (hc : ∀ x, f (ρ x) = π (f x))
    (d : ℕ) (a : Γ) (z : RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a) :
    RawMarkedRetainedOutcome (U:=Z) (Color:=Color) ρ d a :=
  ⟨rawMarkedRestrictPair f g z.1, markedRetainedPairSecond f g π ρ hc d a z.1 z.2⟩

theorem marked_retained_pair_conditional_map
    (f : W ≃ V) (g : Z ≃ U) (π : Equiv.Perm V) (ρ : Equiv.Perm W)
    (hc : ∀ x, f (ρ x) = π (f x)) (d : ℕ) (a : Γ)
    (σ : RawMarkedOutcome V U Γ Color) :
    let A := rawStartHubSet π d (fun e => σ (Sum.inr e)) a
    let B := rawStartHubSet ρ d (fun e => (rawMarkedRestrictPair f g σ) (Sum.inr e)) a
    (startRetentionLaw A (startRetentionMinimum A) (startRetentionMinimum_le A)).map
      (markedRetainedPairSecond f g π ρ hc d a σ) =
    startRetentionLaw B (startRetentionMinimum B) (startRetentionMinimum_le B) := by
  dsimp only
  let A := rawStartHubSet π d (fun e => σ (Sum.inr e)) a
  let B := rawStartHubSet ρ d (fun e => (rawMarkedRestrictPair f g σ) (Sum.inr e)) a
  have he : startRetentionMinimum B = startRetentionMinimum A :=
    raw_marked_retention_minimum_relabel f g π ρ hc d σ a
  have hm : ∀ w x, x ∈ B w ↔ g x ∈ A (f w) :=
    raw_marked_start_hub_mem_relabel f g π ρ hc d σ a
  have h := start_retention_law_inverse_cast f g A B hm (startRetentionMinimum A)
    (startRetentionMinimum B) he (startRetentionMinimum_le A) (startRetentionMinimum_le B)
  have hfun : markedRetainedPairSecond f g π ρ hc d a σ = (fun J =>
      he.symm ▸ (startRetentionRelabelEquiv f g A B hm (startRetentionMinimum A)).symm J) := by
    funext J
    rfl
  rw [hfun]
  exact h
end Oberwolfach
