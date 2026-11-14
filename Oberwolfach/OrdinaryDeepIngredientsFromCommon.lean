module

public import Oberwolfach.OrdinaryDeepParentMargins

@[expose] public section
/-! The common endpoint and deeper events plus an actual cleanup profile
supply all non-hub inputs for the mixed parent on the same raw outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_deep_ingredients_from_common
    (P Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (Z:Finset U)
    (π:Equiv.Perm V) (d:ℕ) (j:Color) (s:U→Color→ℝ) (weight:V→Sym2 (V⊕U)→ℝ)
    (γ κ b B εf η κe p pR pH density tR tH L Ledit βe βh δ ε t K e:ℝ)
    (σ:RawWheelOutcome V U Γ Color)
    (margins:OrdinaryDeepParentMargins P F A Z γ κ b B εf η κe p pR pH density tR tH L Ledit δ ε t K e)
    (hQ:Q≤P\F)
    (profile:OrdinaryCleanupParentProfiles P Q F H π d A Z pR pH density tR tH Ledit βe βh s j σ)
    (deep:RawOrdinaryRows P π d 3 A pR s j tR σ)
    (parent:EndpointPhysicalParentWeights P A Aᶜ weight)
    (event:EndpointPhysicalPotentialEvent P F A Z Aᶜ π d j weight pR pH t σ) :
    OrdinaryDeepParentIngredients P Q F H A Z π d j s weight γ κ b B εf η κe p pR pH density
      tR tH L Ledit βe βh δ ε t K σ := by
  have geom:=endpoint_conditions_from_cleanup_profile P Q F H A Z π d j s κe p pR pH density tR tH L Ledit
    βe βh δ e σ profile margins.Apos hQ margins.kappa_pos margins.p_pos margins.conflict_nonneg margins.edit_nonneg
    margins.delta_nonneg margins.hub_lower margins.hub_upper margins.rim_lower margins.rim_upper margins.spoke_lower
    margins.spoke_upper margins.conflict_degree margins.parent_balance margins.balance_margin
  exact ⟨profile,deep,parent,event,geom,margins.density_lower,margins.conflict_degree,margins.epsilon_nonneg,
    margins.conflict_scale,margins.conflict_inner,margins.row_margin,margins.index_margin,margins.count_error,
    margins.hub_scale,margins.pair_scale,margins.endpoint_scale,margins.parent_degree,margins.scale_nonneg,
    margins.physical_scale,margins.endpoint_error,margins.lower_bound,margins.upper_bound⟩
end Oberwolfach
