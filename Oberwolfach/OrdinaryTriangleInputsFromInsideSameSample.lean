module

public import Oberwolfach.OrdinaryPackingCleanupInputsFromSample
public import Oberwolfach.OrdinaryFreshTriangleBoundaryEventInside

@[expose] public section
/-! The earlier reference and common profiles together with one fresh
reserve/factor event supply both inputs to the controlled triangle level. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
set_option synthInstance.maxSize 2048
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_triangle_level_inputs_from_inside_same_sample
    (k d:ℕ)
    (α ω βsource βparent β b B h ζedit δ εsource εparent εstar η ξ ζreserve p εreserve
      pR pH density tR tH e Ledit βe βh L:ℝ)
    (γ κ bf Bf εf ηf ζf εsupport τ ν:ℝ)
    (P Q Qfactor F:SimpleGraph V) (H Hfactor:V→U→Prop) (π:Equiv.Perm V) (X:Finset V) (Z:Finset U)
    (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color)
    (coins:Sym2 V→Bool) (σ:Sym2 (V⊕U)→Bool)
    (ref:OrdinaryEditedSampleReferenceData 3 (by omega) k α βsource βparent b B h ζedit δ εsource εparent Ledit
      P Q F (rawWheelSpokes π d raw j) H (fun e=>raw (Sum.inl e)) coins)
    (num:OrdinaryUnreservedGeometryNumbers 3 k ω βparent β b B εparent εstar η ξ ζreserve p εreserve
      (e+tR+2*tH+3*Ledit) X Z)
    (profile:OrdinaryCleanupParentProfiles P Q F H π d X Z pR pH density tR tH Ledit βe βh s j raw)
    (htR:0≤tR) (htH:0≤tH) (he:0≤e) (hLedit:0≤Ledit)
    (hparent:∀v,|pR*(P.neighborFinset v∩X).card-2*pH*Z.card|≤e)
    (hF:∀v,(F.degree v:ℝ)≤L)
    (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,3∣(Finset.univ.filter (fun v=>H v u)).card)
    (data:MixedFreshParentDataInsideRoots γ κ bf Bf εf ηf Qfactor F (ordinaryPhysicalGraph Qfactor Hfactor)
      (ordinaryPhysicalGraph F (fun _ _=>False)) (Function.Embedding.inl:V↪V⊕U)
      (ordinaryBoundaryHubSet H Z X) (fun i=>(ordinaryBoundaryRimSet Q X i).image Sum.inl)
      (fun i=>(ordinaryBoundaryRowSet H X Z i).image Sum.inr))
    (fresh:OrdinaryFreshTriangleBoundaryEventInside Q Qfactor F H Hfactor X Z γ κ bf Bf εf ηf ζf p εreserve εsupport βe βh data σ)
    (finishNum:OrdinaryTriangleFinishNumbers (V:=V) (U:=U) γ κ ζf p εsupport τ ν)
    (hbase:ordinaryPhysicalGraph Qfactor Hfactor≤spanningRestriction (ordinaryPhysicalGraph Q H) (ordinaryInnerVertices X Z)):
    OrdinaryPackingCleanupSampleInputs 3 (by omega) k d α ω βparent β b B (h-ζedit) δ εparent εstar η ξ ζreserve p εreserve
      (e+tR+2*tH+3*Ledit) (e+tR+2*tH+3*Ledit)
      pR pH density tR tH Ledit βe βh L P Q F H π X Z s j raw σ ∧
    OrdinaryTriangleFinishSampleInputsInside Q Qfactor F H Hfactor X Z σ γ κ bf Bf εf ηf ζf p εsupport τ ν:=by
  have hQF:Disjoint Q F:=by
    apply disjoint_iff_inf_le.mpr
    intro x y hxy
    exact (ref.graph_sub hxy.1).2 hxy.2
  constructor
  · exact ordinary_packing_cleanup_inputs_from_sample 3 (by omega) k d α ω βsource βparent β b B h ζedit δ
      εsource εparent εstar η ξ ζreserve p εreserve pR pH density tR tH e Ledit βe βh L P Q F H π X Z s j raw
      coins σ ref num profile htR htH he hLedit hparent hF hbal hdiv fresh.reserve fresh.extensions fresh.hub_pairs
  · exact ordinary_triangle_finish_inputs_from_fresh_event_inside Q Qfactor F H Hfactor X Z γ κ bf Bf εf ηf ζf p εreserve
      εsupport βe βh τ ν data σ fresh finishNum hbase hQF hbal hdiv
end Oberwolfach
