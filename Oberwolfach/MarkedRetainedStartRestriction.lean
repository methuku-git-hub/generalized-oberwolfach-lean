module

public import Oberwolfach.MarkedRetainedPairConditional
public import Oberwolfach.RetainedHubMembershipRelabel
public import Oberwolfach.RawIntervalVertexRestriction

@[expose] public section
/-! The outcome relabelling preserves the retained hub membership and the
actual retained starts, including the distinguished marked colour. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z Γ Color : Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
  [Fintype Γ] [Fintype Color] [Nonempty V] [Nonempty W]
  [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]

theorem marked_retained_hub_restriction
    (f : W ≃ V) (g : Z ≃ U) (π : Equiv.Perm V) (ρ : Equiv.Perm W)
    (hc : ∀ x, f (ρ x) = π (f x)) (d : ℕ) (a : Γ)
    (σ : RawMarkedOutcome V U Γ Color)
    (J : StartRetentionOutcome (rawStartHubSet π d (fun e => σ (Sum.inr e)) a)
      (startRetentionMinimum (rawStartHubSet π d (fun e => σ (Sum.inr e)) a)))
    (w : W) (z : Z) :
    let A := rawStartHubSet π d (fun e => σ (Sum.inr e)) a
    let B := rawStartHubSet ρ d (fun e => (rawMarkedRestrictPair f g σ) (Sum.inr e)) a
    z ∈ startRetainedHubs B (startRetentionMinimum B)
      (markedRetainedPairSecond f g π ρ hc d a σ J) w ↔
    g z ∈ startRetainedHubs A (startRetentionMinimum A) J (f w) := by
  dsimp only
  let A := rawStartHubSet π d (fun e => σ (Sum.inr e)) a
  let B := rawStartHubSet ρ d (fun e => (rawMarkedRestrictPair f g σ) (Sum.inr e)) a
  have he : startRetentionMinimum B = startRetentionMinimum A :=
    raw_marked_retention_minimum_relabel f g π ρ hc d σ a
  have hm : ∀ w z, z ∈ B w ↔ g z ∈ A (f w) :=
    raw_marked_start_hub_mem_relabel f g π ρ hc d σ a
  have hh := start_retained_hub_relabel_inverse f g A B hm (startRetentionMinimum A)
    (startRetentionMinimum B) he J w z
  have hfun : markedRetainedPairSecond f g π ρ hc d a σ J =
      he.symm ▸ (startRetentionRelabelEquiv f g A B hm (startRetentionMinimum A)).symm J := by rfl
  rw [hfun]
  exact hh
theorem marked_retained_start_restriction
    (f : W ≃ V) (g : Z ≃ U) (π : Equiv.Perm V) (ρ : Equiv.Perm W)
    (hc : ∀ x, f (ρ x) = π (f x)) (d : ℕ) (a : Γ)
    (σ : RawMarkedOutcome V U Γ Color)
    (J : StartRetentionOutcome (rawStartHubSet π d (fun e => σ (Sum.inr e)) a)
      (startRetentionMinimum (rawStartHubSet π d (fun e => σ (Sum.inr e)) a)))
    (w : W) (z : Z) (c : Γ) :
    let A := rawStartHubSet π d (fun e => σ (Sum.inr e)) a
    let B := rawStartHubSet ρ d (fun e => (rawMarkedRestrictPair f g σ) (Sum.inr e)) a
    retainedRawStart ρ d (fun e => (rawMarkedRestrictPair f g σ) (Sum.inr e)) a
      (startRetentionMinimum B) (markedRetainedPairSecond f g π ρ hc d a σ J) z w c ↔
    retainedRawStart π d (fun e => σ (Sum.inr e)) a
      (startRetentionMinimum A) J (g z) (f w) c := by
  dsimp only
  have hs : (fun e => (rawMarkedRestrictPair f g σ) (Sum.inr (z,e))) =
      rawIntervalRestrictVertices f (fun e => σ (Sum.inr (g z,e))) := by
    funext e
    cases e with
    | inl e => rfl
    | inr e => cases e <;> rfl
  have hr := rawIntervalColouredStart_restrict f f.injective π ρ hc d
    (fun e => σ (Sum.inr (g z,e))) w c
  rw [← hs] at hr
  have hh := marked_retained_hub_restriction f g π ρ hc d a σ J w z
  unfold retainedRawStart
  constructor
  · rintro ⟨hstart,hkeep⟩
    exact ⟨hr.mp hstart, fun he => hh.mp (hkeep he)⟩
  · rintro ⟨hstart,hkeep⟩
    exact ⟨hr.mpr hstart, fun he => hh.mpr (hkeep he)⟩
end Oberwolfach
