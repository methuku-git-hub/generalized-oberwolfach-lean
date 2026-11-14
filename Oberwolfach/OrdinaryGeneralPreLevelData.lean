module

public import Oberwolfach.OrdinaryPackingCleanupInputsFromSample
public import Oberwolfach.OrdinaryGeneralFinishSampleInputs

@[expose] public section
/-! Explicit reference, cleanup and general-length finish data on one
original/fresh sample; the surrounding probability and hierarchy remain open. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option synthInstance.maxSize 8192
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

structure OrdinaryGeneralPreLevelData
    (m k d:ℕ) (hm:3≤m)
    (α ω βsource βparent β b B h ζedit δ εsource εparent εstar η ξ ζreserve p εreserve
      pR pH density tR tH e Ledit βe βh L τ ν κ ζf εsupport:ℝ)
    (Dmax Kcap:ℕ)
    (P Q F:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V) (X:Finset V) (Z:Finset U)
    (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color)
    (coins:Sym2 V→Bool) (σ:Sym2 (V⊕U)→Bool) where
  reference:OrdinaryEditedSampleReferenceData (m+1) (by omega) k α βsource βparent b B h ζedit δ εsource εparent Ledit
    P Q F (rawWheelSpokes π d raw j) H (fun e=>raw (Sum.inl e)) coins
  numbers:OrdinaryUnreservedGeometryNumbers (m+1) k ω βparent β b B εparent εstar η ξ ζreserve p εreserve
    (e+tR+2*tH+3*Ledit) X Z
  row_nonneg:0≤tR
  column_nonneg:0≤tH
  balance_nonneg:0≤e
  edit_nonneg:0≤Ledit
  parent_balance:∀v,|pR*(P.neighborFinset v∩X).card-2*pH*Z.card|≤e
  reserve:OrdinaryBoundaryReserveGood Q H X Z p εreserve σ
  extensions:OrdinaryBoundaryExtensionGood Q H X βe p σ
  hub_pairs:OrdinaryBoundaryHubPairGood H Z βh p σ
  finish:OrdinaryGeneralFinishSampleInputs m d P Q F H π X Z σ pR pH p density tR tH Ledit βe βh
    (τ*Fintype.card (V⊕U)) (ν*Fintype.card (V⊕U)) κ ζf εsupport Dmax Kcap L s j raw

theorem ordinary_general_inputs_from_prelevel
    (m k d:ℕ) (hm:3≤m)
    (α ω βsource βparent β b B h ζedit δ εsource εparent εstar η ξ ζreserve p εreserve
      pR pH density tR tH e Ledit βe βh L τ ν κ ζf εsupport:ℝ)
    (Dmax Kcap:ℕ)
    (P Q F:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V) (X:Finset V) (Z:Finset U)
    (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color)
    (coins:Sym2 V→Bool) (σ:Sym2 (V⊕U)→Bool)
    (data:OrdinaryGeneralPreLevelData m k d hm α ω βsource βparent β b B h ζedit δ εsource εparent εstar η ξ ζreserve p εreserve
      pR pH density tR tH e Ledit βe βh L τ ν κ ζf εsupport Dmax Kcap P Q F H π X Z s j raw coins σ):
    OrdinaryPackingCleanupSampleInputs (m+1) (by omega) k d α ω βparent β b B (h-ζedit) δ εparent εstar η ξ ζreserve p εreserve
      (e+tR+2*tH+3*Ledit) (e+tR+2*tH+3*Ledit)
      pR pH density tR tH Ledit βe βh L P Q F H π X Z s j raw σ ∧
    OrdinaryGeneralFinishSampleInputs m d P Q F H π X Z σ pR pH p density tR tH Ledit βe βh
      (τ*Fintype.card (V⊕U)) (ν*Fintype.card (V⊕U)) κ ζf εsupport Dmax Kcap L s j raw:=by
  constructor
  · exact ordinary_packing_cleanup_inputs_from_sample (m+1) (by omega) k d α ω βsource βparent β b B h ζedit δ
      εsource εparent εstar η ξ ζreserve p εreserve pR pH density tR tH e Ledit βe βh L P Q F H π X Z s j raw
      coins σ data.reference data.numbers data.finish.profile data.row_nonneg data.column_nonneg data.balance_nonneg data.edit_nonneg
      data.parent_balance data.finish.conflict_degree data.finish.balance data.finish.divisible data.reserve data.extensions data.hub_pairs
  · exact data.finish
end Oberwolfach
