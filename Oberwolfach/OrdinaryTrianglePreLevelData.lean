module

public import Oberwolfach.OrdinaryTriangleInputsFromInsideSameSample

@[expose] public section
/-! Explicit data on one earlier/fresh sample for the controlled triangle
level, retaining the selected parent and fresh boundary factors. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2600000
set_option synthInstance.maxSize 8192
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

structure OrdinaryTrianglePreLevelData
    (k d:ℕ)
    (α ω βsource βparent β b B h ζedit δ εsource εparent εstar η ξ ζreserve p εreserve
      pR pH density tR tH e Ledit βe βh L:ℝ)
    (γ κ bf Bf εf ηf ζf εsupport τ ν:ℝ)
    (P Q Qfactor F:SimpleGraph V) (H Hfactor:V→U→Prop) (π:Equiv.Perm V) (X:Finset V) (Z:Finset U)
    (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color)
    (coins:Sym2 V→Bool) (σ:Sym2 (V⊕U)→Bool) where
  reference : OrdinaryEditedSampleReferenceData 3 (by omega) k α βsource βparent b B h ζedit δ εsource εparent Ledit
    P Q F (rawWheelSpokes π d raw j) H (fun e=>raw (Sum.inl e)) coins
  numbers : OrdinaryUnreservedGeometryNumbers 3 k ω βparent β b B εparent εstar η ξ ζreserve p εreserve
    (e+tR+2*tH+3*Ledit) X Z
  profile : OrdinaryCleanupParentProfiles P Q F H π d X Z pR pH density tR tH Ledit βe βh s j raw
  row_nonneg : 0≤tR
  column_nonneg : 0≤tH
  balance_nonneg : 0≤e
  edit_nonneg : 0≤Ledit
  parent_balance : ∀v,|pR*(P.neighborFinset v∩X).card-2*pH*Z.card|≤e
  conflict_degree : ∀v,(F.degree v:ℝ)≤L
  balanced : ∀v,Q.degree v=2*(Finset.univ.filter (H v)).card
  divisible : ∀u,3∣(Finset.univ.filter (fun v=>H v u)).card
  parent : MixedFreshParentDataInsideRoots γ κ bf Bf εf ηf Qfactor F (ordinaryPhysicalGraph Qfactor Hfactor)
    (ordinaryPhysicalGraph F (fun _ _=>False)) (Function.Embedding.inl:V↪V⊕U)
    (ordinaryBoundaryHubSet H Z X) (fun i=>(ordinaryBoundaryRimSet Q X i).image Sum.inl)
    (fun i=>(ordinaryBoundaryRowSet H X Z i).image Sum.inr)
  fresh : OrdinaryFreshTriangleBoundaryEventInside Q Qfactor F H Hfactor X Z γ κ bf Bf εf ηf ζf p εreserve εsupport βe βh parent σ
  finish_numbers : OrdinaryTriangleFinishNumbers (V:=V) (U:=U) γ κ ζf p εsupport τ ν
  base_inclusion : ordinaryPhysicalGraph Qfactor Hfactor≤spanningRestriction (ordinaryPhysicalGraph Q H) (ordinaryInnerVertices X Z)
end Oberwolfach
