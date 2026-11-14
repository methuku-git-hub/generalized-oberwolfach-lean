module

public import Oberwolfach.FirstVortexTransferStableSelectorMargins

@[expose] public section
/-! The change-graph bounds produced by the matching correction use the same
ambient cap as the selected-parent transfers. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_correction_transfer_graph_bounds
    {n:ℕ} {U:Type} [Fintype U]
    (FR:SimpleGraph (Fin n)) (FS:SimpleGraph (Fin n⊕U))
    (cap ζ ηphys ηdel ηtype:ℝ)
    (hcap:ηphys+ηdel+ηtype≤cap*n) (hζ:ζ≤cap)
    (hFR:∀v,(FR.degree v:ℝ)≤ηphys+ηdel+ηtype)
    (hFS:∀z,(FS.degree z:ℝ)≤ζ*n):
    (∀v,(FR.degree v:ℝ)≤cap*Fintype.card (Fin n)) ∧
    (∀z,(FS.degree z:ℝ)≤cap*Fintype.card (Fin n)) :=by
  constructor
  · intro v
    simpa only [Fintype.card_fin] using (hFR v).trans hcap
  · intro z
    have hm:=mul_le_mul_of_nonneg_right hζ (show (0:ℝ)≤n by positivity)
    simpa only [Fintype.card_fin] using (hFS z).trans hm
end Oberwolfach
