module

public import Oberwolfach.RawIntervalVertexRestriction
public import Oberwolfach.RetainedIntervalGeometry

@[expose] public section
/-! Relabelling all permutation starts preserves the interval state when the
retained-start relation is transported pointwise. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W Γ Color : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

theorem retained_interval_state_relabel
    (f : W ≃ V) (π : Equiv.Perm V) (ρ : Equiv.Perm W)
    (hc : ∀ x, f (ρ x) = π (f x)) (d : ℕ)
    (σ : RawIntervalOutcome V Γ Color) (R : V → Γ → Prop) (S : W → Γ → Prop)
    (hR : ∀ w c, S w c ↔ R (f w) c) (x : W) :
    retainedIntervalState ρ d (rawIntervalRestrictVertices f σ) S x =
    retainedIntervalState π d σ R (f x) := by
  have hcover : retainedIntervalCovered ρ d S x = retainedIntervalCovered π d R (f x) := by
    funext c
    apply propext
    constructor
    · rintro ⟨w,hw,hx⟩
      exact ⟨f w,(hR w c).mp hw,
        (permutationWindow_embedding_mem f π ρ hc f.injective 0 (d-1) w x).mpr hx⟩
    · rintro ⟨v,hv,hx⟩
      refine ⟨f.symm v, ?_, ?_⟩
      · apply (hR (f.symm v) c).mpr
        simpa only [Equiv.apply_symm_apply] using hv
      · apply (permutationWindow_embedding_mem f π ρ hc f.injective 0 (d-1) (f.symm v) x).mp
        simpa only [Equiv.apply_symm_apply] using hx
  have hblocked : retainedIntervalBlocked ρ d S x ↔ retainedIntervalBlocked π d R (f x) := by
    constructor
    · rintro ⟨c,w,hw,hx⟩
      exact ⟨c,f w,(hR w c).mp hw,
        (permutationWindow_embedding_mem f π ρ hc f.injective 0 d w x).mpr hx⟩
    · rintro ⟨c,v,hv,hx⟩
      refine ⟨c,f.symm v, ?_, ?_⟩
      · apply (hR (f.symm v) c).mpr
        simpa only [Equiv.apply_symm_apply] using hv
      · apply (permutationWindow_embedding_mem f π ρ hc f.injective 0 d (f.symm v) x).mp
        simpa only [Equiv.apply_symm_apply] using hx
  have hb : retainedIntervalBlocked ρ d S x = retainedIntervalBlocked π d R (f x) := propext hblocked
  unfold retainedIntervalState
  rw [hcover,hb]
  rfl
end Oberwolfach
