module

public import Oberwolfach.MarkedNeighbourhoodSpokeChanges

@[expose] public section
/-! A row estimate with a fixed physical spoke relation depends only on the
rim coordinates of the raw outcome. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_rows_with_spokes_rim_equality
    (P:SimpleGraph V) (π:Equiv.Perm V) (d h:ℕ) (A:Finset V) (p k:ℝ)
    (q:U→Γ→ℝ) (s:U→Color→ℝ) (a:Γ) (j:Color) (err:ℝ)
    (σ τ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hrim:∀ e,τ (Sum.inl e)=σ (Sum.inl e))
    (hrow:MarkedRowsWithSpokes P π d h A p k q s a j err σ H):
    MarkedRowsWithSpokes P π d h A p k q s a j err τ H:=by
  have heq:(fun e=>τ (Sum.inl e))=(fun e=>σ (Sum.inl e)):=funext hrim
  unfold MarkedRowsWithSpokes markedRowCountWithSpokes at hrow ⊢
  unfold rawMarkedPairRims at hrow ⊢
  rw [heq]
  exact hrow
end Oberwolfach
