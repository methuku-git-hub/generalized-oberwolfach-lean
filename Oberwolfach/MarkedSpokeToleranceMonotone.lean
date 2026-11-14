module

public import Oberwolfach.MarkedNeighbourhoodSpokeChanges

@[expose] public section
/-! A single common neighbourhood estimate supplies all larger error
allowances without changing the domains or the sample. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]
theorem marked_rows_with_spokes_tolerance_mono
    (P:SimpleGraph V) (π:Equiv.Perm V) (d h:ℕ) (A:Finset V) (p k:ℝ)
    (q:U→Γ→ℝ) (s:U→Color→ℝ) (g:Γ) (j:Color) (ε ε':ℝ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop) (hle:ε≤ε'):
    MarkedRowsWithSpokes P π d h A p k q s g j ε σ H→
      MarkedRowsWithSpokes P π d h A p k q s g j ε' σ H:=by
  intro hh S T J hS hT hJ hinj
  exact (hh S T J hS hT hJ hinj).trans_le hle

theorem marked_indices_with_spokes_tolerance_mono
    (π:Equiv.Perm V) (d h:ℕ) (A:Finset U)
    (q:U→Γ→ℝ) (s:U→Color→ℝ) (g:Γ) (j:Color) (ε ε':ℝ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop) (hle:ε≤ε'):
    MarkedIndicesWithSpokes π d h A q s g j ε σ H→
      MarkedIndicesWithSpokes π d h A q s g j ε' σ H:=by
  intro hh J hJ hsep
  exact (hh J hJ hsep).trans_le hle
end Oberwolfach
