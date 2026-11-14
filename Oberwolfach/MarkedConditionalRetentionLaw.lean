module

public import Oberwolfach.MarkedRetentionReindex
public import Oberwolfach.RetentionLawRelabel

@[expose] public section
/-! For a fixed raw marked outcome, transport the actual conditional law of
retaining uniformly chosen eligible hubs at each start. The outer raw law is
not changed or coupled in this statement. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z Γ Color : Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
  [Fintype Γ] [Fintype Color] [Nonempty V] [Nonempty W]
  [DecidableEq V] [DecidableEq W] [DecidableEq U] [DecidableEq Z]

theorem marked_conditional_retention_law_relabel
    (f : W ≃ V) (g : Z ≃ U) (π : Equiv.Perm V) (ρ : Equiv.Perm W)
    (hc : ∀ x, f (ρ x) = π (f x)) (d : ℕ)
    (σ : RawMarkedOutcome V U Γ Color) (a : Γ) :
    let A := rawStartHubSet π d (fun e => σ (Sum.inr e)) a
    let B := rawStartHubSet ρ d (fun e => (rawMarkedRestrictPair f g σ) (Sum.inr e)) a
    let t := startRetentionMinimum A
    let ht : ∀ v, t ≤ (A v).card := startRetentionMinimum_le A
    let ht' : ∀ w, t ≤ (B w).card := fun w =>
      (by change startRetentionMinimum A ≤ (B w).card; have he : startRetentionMinimum B = startRetentionMinimum A := raw_marked_retention_minimum_relabel f g π ρ hc d σ a; rw [← he]; exact startRetentionMinimum_le B w)
    let hmem : ∀ w z, z ∈ B w ↔ g z ∈ A (f w) :=
      raw_marked_start_hub_mem_relabel f g π ρ hc d σ a
    ∀ E : StartRetentionOutcome A t → Prop,
      (startRetentionLaw A t ht).probability E =
        (startRetentionLaw B t ht').probability (fun J =>
          E (Equiv.piCongrLeft (fun v => FixedSubset {u // u ∈ A v} t) f
            (fun w => fixedSubsetRelabelEquiv (eligibleHubEquiv f g A B hmem w) (J w)))) := by
  dsimp only
  intro E
  exact start_retention_law_relabel f g _ _ _ _ _ _ E
end Oberwolfach
