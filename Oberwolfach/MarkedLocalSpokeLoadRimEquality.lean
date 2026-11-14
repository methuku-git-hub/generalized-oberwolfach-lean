module

public import Oberwolfach.MarkedLocalLoadSpokeChanges

@[expose] public section
/-! A local spoke-root load uses the rim states and the supplied physical
spoke relation; the other coordinates of the raw outcome do not enter. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_local_spoke_loads_rim_equality
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (D p k s₀:ℝ)
    (weight:(Fin (m+1)→V)→ℝ) (η:ℝ)
    (σ τ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hrim:∀ e,τ (Sum.inl e)=σ (Sum.inl e))
    (h:MarkedLocalSpokeLoadsWithSpokes P π d m D p k s₀ weight η σ H):
    MarkedLocalSpokeLoadsWithSpokes P π d m D p k s₀ weight η τ H:=by
  have heq:(fun e=>τ (Sum.inl e))=(fun e=>σ (Sum.inl e)):=funext hrim
  unfold MarkedLocalSpokeLoadsWithSpokes at h ⊢
  unfold rawMarkedPairRims at h ⊢
  rw [heq]
  exact h
end Oberwolfach
