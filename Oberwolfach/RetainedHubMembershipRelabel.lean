module

public import Oberwolfach.RetentionLawRelabel

@[expose] public section
/-! The relabelling of conditional outcomes also preserves the actual
retained hubs, not just their probability law. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z : Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
  [DecidableEq V] [DecidableEq W] [DecidableEq U] [DecidableEq Z]

theorem start_retained_hub_relabel
    (f : W ≃ V) (g : Z ≃ U) (A : V → Finset U) (B : W → Finset Z)
    (h : ∀ w z, z ∈ B w ↔ g z ∈ A (f w)) (t : ℕ)
    (J : StartRetentionOutcome B t) (w : W) (z : Z) :
    z ∈ startRetainedHubs B t J w ↔
      g z ∈ startRetainedHubs A t (startRetentionRelabelEquiv f g A B h t J) (f w) := by
  simp only [startRetainedHubs, startRetentionRelabelEquiv, Equiv.trans_apply,
    Equiv.piCongrLeft_apply_apply, Equiv.piCongrRight_apply, Pi.map_apply,
    fixedSubsetRelabelEquiv, Equiv.coe_fn_mk, Finset.mem_map, Function.Embedding.subtype_apply]
  constructor
  · rintro ⟨v,hv,hz⟩
    refine ⟨eligibleHubEquiv f g A B h w v, ?_, ?_⟩
    · exact ⟨v,hv,rfl⟩
    · change g v.val = g z
      rw [hz]
  · rintro ⟨u,hu,huval⟩
    obtain ⟨v,hv,hvu⟩ := hu
    refine ⟨v,hv,?_⟩
    apply g.injective
    change g v.val = g z
    rw [← huval]
    exact congrArg Subtype.val hvu
theorem start_retained_hub_relabel_inverse
    (f : W ≃ V) (g : Z ≃ U) (A : V → Finset U) (B : W → Finset Z)
    (h : ∀ w z, z ∈ B w ↔ g z ∈ A (f w)) (t u : ℕ) (he : u = t)
    (J : StartRetentionOutcome A t) (w : W) (z : Z) :
    z ∈ startRetainedHubs B u (he.symm ▸ (startRetentionRelabelEquiv f g A B h t).symm J) w ↔
      g z ∈ startRetainedHubs A t J (f w) := by
  cases he
  have hh := start_retained_hub_relabel f g A B h t
    ((startRetentionRelabelEquiv f g A B h t).symm J) w z
  rw [Equiv.apply_symm_apply] at hh
  exact hh
end Oberwolfach
