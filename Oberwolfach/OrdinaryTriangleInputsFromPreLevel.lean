module

public import Oberwolfach.OrdinaryTrianglePreLevelData

@[expose] public section
/-! The retained same-sample data supply both packing/cleanup and triangle
finish inputs for the controlled level theorem. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 8192
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_triangle_inputs_from_prelevel
    (k d:ℕ)
    (α ω βsource βparent β b B h ζedit δ εsource εparent εstar η ξ ζreserve p εreserve
      pR pH density tR tH e Ledit βe βh L:ℝ)
    (γ κ bf Bf εf ηf ζf εsupport τ ν:ℝ)
    (P Q Qfactor F:SimpleGraph V) (H Hfactor:V→U→Prop) (π:Equiv.Perm V) (X:Finset V) (Z:Finset U)
    (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color)
    (coins:Sym2 V→Bool) (σ:Sym2 (V⊕U)→Bool)
    (data:OrdinaryTrianglePreLevelData k d α ω βsource βparent β b B h ζedit δ εsource εparent εstar η ξ ζreserve p εreserve
      pR pH density tR tH e Ledit βe βh L γ κ bf Bf εf ηf ζf εsupport τ ν P Q Qfactor F H Hfactor π X Z s j raw coins σ) :
    OrdinaryPackingCleanupSampleInputs 3 (by omega) k d α ω βparent β b B (h-ζedit) δ εparent εstar η ξ ζreserve p εreserve
      (e+tR+2*tH+3*Ledit) (e+tR+2*tH+3*Ledit)
      pR pH density tR tH Ledit βe βh L P Q F H π X Z s j raw σ ∧
    OrdinaryTriangleFinishSampleInputsInside Q Qfactor F H Hfactor X Z σ γ κ bf Bf εf ηf ζf p εsupport τ ν := by
  exact ordinary_triangle_level_inputs_from_inside_same_sample k d α ω βsource βparent β b B h ζedit δ εsource εparent
    εstar η ξ ζreserve p εreserve pR pH density tR tH e Ledit βe βh L γ κ bf Bf εf ηf ζf εsupport τ ν
    P Q Qfactor F H Hfactor π X Z s j raw coins σ data.reference data.numbers data.profile data.row_nonneg data.column_nonneg
    data.balance_nonneg data.edit_nonneg data.parent_balance data.conflict_degree data.balanced data.divisible data.parent
    data.fresh data.finish_numbers data.base_inclusion
end Oberwolfach
