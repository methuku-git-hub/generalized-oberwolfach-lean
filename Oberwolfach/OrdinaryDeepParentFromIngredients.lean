module

public import Oberwolfach.OrdinaryDeepParentIngredients

@[expose] public section
/-! The same-sample deep/endpoint ingredients and hub weights construct the
corrected local-root mixed parent without changing the selected host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2500000
set_option synthInstance.maxSize 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

def ordinary_deep_parent_from_ingredients
    (P Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (Z:Finset U)
    (π:Equiv.Perm V) (d:ℕ) (j:Color) (s:U→Color→ℝ) (weight:V→Sym2 (V⊕U)→ℝ)
    (γ κ b B εf η κe p pR pH density tR tH L Ledit βe βh δ ε t K:ℝ)
    (σ:RawWheelOutcome V U Γ Color)
    (inputs:OrdinaryDeepParentIngredients P Q F H A Z π d j s weight γ κ b B εf η κe p pR pH density
      tR tH L Ledit βe βh δ ε t K σ)
    (hw:OrdinaryMixedHubWeights b B η Q F H A Z) :
    MixedFreshParentDataInsideRoots γ κ b B εf η (spanningRestriction Q A) F
      (ordinaryPhysicalGraph (spanningRestriction Q A) (fun v u=>H v u∧v∈A∧u∈Z))
      (ordinaryPhysicalGraph F (fun _ _=>False)) (Function.Embedding.inl:V↪V⊕U)
      (ordinaryBoundaryHubSet H Z A) (fun i=>(ordinaryBoundaryRimSet Q A i).image Sum.inl)
      (fun i=>(ordinaryBoundaryRowSet H A Z i).image Sum.inr) := by
  exact ordinary_mixed_parent_from_deep_sample_inside P Q F H A Z π d j s weight γ κ b B εf η κe p pR pH density
    tR tH L Ledit βe βh δ ε t K σ inputs.profile inputs.deep inputs.parent inputs.endpoint_event inputs.geom hw
    inputs.density_lower inputs.conflict_degree inputs.epsilon_nonneg inputs.conflict_scale inputs.conflict_inner
    inputs.row_margin inputs.index_margin inputs.count_error inputs.hub_scale inputs.pair_scale inputs.endpoint_scale
    inputs.parent_degree inputs.scale_nonneg inputs.physical_scale inputs.endpoint_error inputs.lower_bound inputs.upper_bound
end Oberwolfach
