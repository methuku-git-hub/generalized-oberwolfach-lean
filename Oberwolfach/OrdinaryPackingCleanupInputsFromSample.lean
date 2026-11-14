module

public import Oberwolfach.OrdinaryUnreservedParentFromSample
public import Oberwolfach.OrdinaryUnreservedGeometryFromCommonSample
public import Oberwolfach.OrdinaryPackingCleanupSampleInputs

@[expose] public section
/-! Assemble the packing-and-cleanup input on the same earlier sample and
fresh reserve, using the common balance profiles and extension events. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
set_option synthInstance.maxSize 2048
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_packing_cleanup_inputs_from_sample
    (r:ℕ) (hr:3≤r) (k d:ℕ)
    (α ω βsource βparent β b B h ζedit δ εsource εparent εstar η ξ ζreserve p ε
      pR pH density tR tH e Ledit βe βh L:ℝ)
    (P Q F:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V) (X:Finset V) (Z:Finset U)
    (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color)
    (coins:Sym2 V→Bool) (σ:Sym2 (V⊕U)→Bool)
    (ref:OrdinaryEditedSampleReferenceData r hr k α βsource βparent b B h ζedit δ εsource εparent Ledit
      P Q F (rawWheelSpokes π d raw j) H (fun e=>raw (Sum.inl e)) coins)
    (num:OrdinaryUnreservedGeometryNumbers r k ω βparent β b B εparent εstar η ξ ζreserve p ε
      (e+tR+2*tH+3*Ledit) X Z)
    (profile:OrdinaryCleanupParentProfiles P Q F H π d X Z pR pH density tR tH Ledit βe βh s j raw)
    (htR:0≤tR) (htH:0≤tH) (he:0≤e) (hLedit:0≤Ledit)
    (hparent:∀v,|pR*(P.neighborFinset v∩X).card-2*pH*Z.card|≤e)
    (hF:∀v,(F.degree v:ℝ)≤L)
    (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,r∣(Finset.univ.filter (fun v=>H v u)).card)
    (hgood:OrdinaryBoundaryReserveGood Q H X Z p ε σ)
    (hext:OrdinaryBoundaryExtensionGood Q H X βe p σ)
    (hpair:OrdinaryBoundaryHubPairGood H Z βh p σ):
    OrdinaryPackingCleanupSampleInputs r hr k d α ω βparent β b B (h-ζedit) δ εparent εstar η ξ ζreserve p ε
      (e+tR+2*tH+3*Ledit) (e+tR+2*tH+3*Ledit)
      pR pH density tR tH Ledit βe βh L P Q F H π X Z s j raw σ:=by
  have hrim:∀v,((changed ((rawWheelGraph P raw).neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤Ledit:=by
    simpa only [rawWheelGraph] using ref.rim_edit
  have geo:=ordinary_unreserved_geometry_from_common_sample r k d ω βparent β b B εparent εstar η ξ ζreserve p ε
    pR pH tR tH e Ledit P Q F H X Z π s j raw σ num htR htH he hLedit profile.rows profile.columns
    hparent hrim ref.spoke_row_edit hbal hgood
  have parent:=ordinary_unreserved_parent_data_from_sample r hr k α ω βsource βparent β b B h ζedit δ
    εsource εparent εstar η ξ ζreserve p ε (e+tR+2*tH+3*Ledit) (e+tR+2*tH+3*Ledit) Ledit
    P Q F (rawWheelSpokes π d raw j) H X Z (fun e=>raw (Sum.inl e)) coins σ ref geo
  exact ⟨parent,profile,hF,hbal,hdiv,hext,hpair⟩
end Oberwolfach
