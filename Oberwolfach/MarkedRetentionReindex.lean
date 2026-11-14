module

public import Oberwolfach.RawMarkedPairRestriction
public import Oberwolfach.RetainedIntervalFamily
public import Oberwolfach.RawIntervalVertexRestriction
public import Oberwolfach.RetentionMinimumRelabel

@[expose] public section
/-! Exact relabelling of the eligible hub sets, before any retention is sampled. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z Γ Color : Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
  [Fintype Γ] [Fintype Color] [Nonempty V] [Nonempty W]
  [DecidableEq V] [DecidableEq W] [DecidableEq U] [DecidableEq Z]

theorem raw_marked_start_hub_mem_relabel
    (f : W ≃ V) (g : Z ≃ U) (π : Equiv.Perm V) (ρ : Equiv.Perm W)
    (hc : ∀ x, f (ρ x) = π (f x)) (d : ℕ)
    (σ : RawMarkedOutcome V U Γ Color) (a : Γ) (x : W) (z : Z) :
    z ∈ rawStartHubSet ρ d (fun e => (rawMarkedRestrictPair f g σ) (Sum.inr e)) a x ↔
    g z ∈ rawStartHubSet π d (fun e => σ (Sum.inr e)) a (f x) := by
  simp only [rawStartHubSet, Finset.mem_filter, Finset.mem_univ, true_and]
  have hs : (fun e => (rawMarkedRestrictPair f g σ) (Sum.inr (z,e))) =
      rawIntervalRestrictVertices f (fun e => σ (Sum.inr (g z,e))) := by
    funext e
    cases e with
    | inl e => rfl
    | inr e => cases e <;> rfl
  rw [hs]
  exact rawIntervalColouredStart_restrict f f.injective π ρ hc d _ x a

theorem raw_marked_start_hub_relabel
    (f : W ≃ V) (g : Z ≃ U) (π : Equiv.Perm V) (ρ : Equiv.Perm W)
    (hc : ∀ x, f (ρ x) = π (f x)) (d : ℕ)
    (σ : RawMarkedOutcome V U Γ Color) (a : Γ) (x : W) :
    (rawStartHubSet ρ d (fun e => (rawMarkedRestrictPair f g σ) (Sum.inr e)) a x).card =
    (rawStartHubSet π d (fun e => σ (Sum.inr e)) a (f x)).card := by
  apply Finset.card_bij (fun z _ => g z)
  · intro z hz
    simp only [rawStartHubSet, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    have hs : (fun e => (rawMarkedRestrictPair f g σ) (Sum.inr (z,e))) =
        rawIntervalRestrictVertices f (fun e => σ (Sum.inr (g z,e))) := by
      funext e
      cases e with
      | inl e => rfl
      | inr e => cases e <;> rfl
    rw [hs] at hz
    exact (rawIntervalColouredStart_restrict f f.injective π ρ hc d _ x a).mp hz
  · intro z hz z' hz' heq
    exact g.injective heq
  · intro u hu
    refine ⟨g.symm u, ?_, g.apply_symm_apply u⟩
    simp only [rawStartHubSet, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    have hs : (fun e => (rawMarkedRestrictPair f g σ) (Sum.inr (g.symm u,e))) =
        rawIntervalRestrictVertices f (fun e => σ (Sum.inr (u,e))) := by
      funext e
      cases e with
      | inl e => simp [rawMarkedRestrictPair, rawMarkedRestrictVertices, rawMarkedRestrictHubs, rawIntervalRestrictVertices, rawMarkedVertexState, rawMarkedHubState, rawMarkedVertexCoordinate, rawMarkedHubCoordinate, rawIntervalVertexCoordinate] <;> rw [g.apply_symm_apply]
      | inr e => cases e <;> simp [rawMarkedRestrictPair, rawMarkedRestrictVertices, rawMarkedRestrictHubs, rawIntervalRestrictVertices, rawMarkedVertexState, rawMarkedHubState, rawMarkedVertexCoordinate, rawMarkedHubCoordinate, rawIntervalVertexCoordinate] <;> rw [g.apply_symm_apply]
    rw [hs]
    exact (rawIntervalColouredStart_restrict f f.injective π ρ hc d _ x a).mpr hu

theorem raw_marked_retention_minimum_relabel
    (f : W ≃ V) (g : Z ≃ U) (π : Equiv.Perm V) (ρ : Equiv.Perm W)
    (hc : ∀ x, f (ρ x) = π (f x)) (d : ℕ)
    (σ : RawMarkedOutcome V U Γ Color) (a : Γ) :
    startRetentionMinimum (rawStartHubSet ρ d (fun e => (rawMarkedRestrictPair f g σ) (Sum.inr e)) a) =
    startRetentionMinimum (rawStartHubSet π d (fun e => σ (Sum.inr e)) a) := by
  apply start_retention_minimum_relabel f
  intro x
  exact raw_marked_start_hub_relabel f g π ρ hc d σ a x
end Oberwolfach
