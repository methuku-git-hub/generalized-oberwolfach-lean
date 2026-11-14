module

public import Oberwolfach.MarkedReferenceDeletionState

@[expose] public section
/-! A fixed deletion remains valid when its two incidence budgets increase. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_reference_deletion_valid_loss_mono
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]
    {P:SimpleGraph V} {π:Equiv.Perm V} {d:ℕ} {σ:RawMarkedOutcome V U Γ Color}
    (D:MarkedReferenceDeletion P π d σ) (H:Bool→V→U→Prop)
    (m:ℕ) (X:Finset V) (Y:Finset U) (γsmall σsmall γlarge σlarge:ℝ)
    (hγ:γsmall≤γlarge) (hσ:σsmall≤σlarge)
    (hv:D.Valid H m X Y γsmall σsmall):D.Valid H m X Y γlarge σlarge :=by
  change _ ∧ _ ∧ _ ∧ _ ∧ _ at hv ⊢
  exact ⟨hv.1,hv.2.1,fun v u=>(hv.2.2.1 v u).trans hγ,
    fun v u=>(hv.2.2.2.1 v u).trans hσ,hv.2.2.2.2⟩
end Oberwolfach
