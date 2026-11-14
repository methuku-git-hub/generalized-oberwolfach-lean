module

public import Oberwolfach.OrdinaryBoundaryLocalEvents

@[expose] public section
/-! A retained extension event on a subset also holds on the full set. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_boundary_extension_event_subset_mono
    (Q:SimpleGraph V) (H:V→U→Prop) (Y X:Finset V) (hYX:Y⊆X)
    (β p:ℝ) (σ:Sym2 (V⊕U)→Bool)
    (hgood:OrdinaryBoundaryExtensionGood Q H Y β p σ):
    OrdinaryBoundaryExtensionGood Q H X β p σ :=by
  intro a c u
  apply (hgood a c u).trans
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro v hv
  simp only [retainedPatternSet, Finset.mem_filter] at hv ⊢
  exact ⟨⟨hYX hv.1.1,hv.1.2⟩,hv.2⟩
end Oberwolfach
