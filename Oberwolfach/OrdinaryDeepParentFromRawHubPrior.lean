module

public import Oberwolfach.OrdinaryRawHubParentPrior
public import Oberwolfach.OrdinaryDeepIngredientsFromCommon
public import Oberwolfach.OrdinaryDeepParentFromIngredients

@[expose] public section
/-! The full raw prior supplies endpoint and size-three deep inputs for
    every later cleanup, on the same original sampled outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_deep_ingredients_from_raw_hub_prior
    (P Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (Z:Finset U)
    (π:Equiv.Perm V) (d k:ℕ) (j:Color) (s:U→Color→ℝ)
    (weight:V→Sym2 (V⊕U)→ℝ) (triangleWeight:OrdinaryCycle P 3→ℝ)
    (γ κ b B εf η κe p pR pH density tR tH L Ledit βe βh δ ε t Kscale e:ℝ)
    (α pstar βP ηP ηH βH c Btri:ℝ) (σ:RawWheelOutcome V U Γ Color)
    (margins:OrdinaryDeepParentMargins P F A Z γ κ b B εf η κe p pR pH density tR tH L Ledit δ ε t Kscale e)
    (hQ:Q≤P\F)
    (profile:OrdinaryCleanupParentProfiles P Q F H π d A Z pR pH density tR tH Ledit βe βh s j σ)
    (parent:EndpointPhysicalParentWeights P A Aᶜ weight)
    (event:OrdinaryRawHubParentPrior d k P F A Z π j s weight triangleWeight
      α pstar βP ηP ηH βH c Btri pR pH t tR tH σ) :
    OrdinaryDeepParentIngredients P Q F H A Z π d j s weight γ κ b B εf η κe p pR pH density
      tR tH L Ledit βe βh δ ε t Kscale σ := by
  exact ordinary_deep_ingredients_from_common P Q F H A Z π d j s weight γ κ b B εf η κe p pR pH density
    tR tH L Ledit βe βh δ ε t Kscale e σ margins hQ profile event.2.2.1 parent event.2.1

def ordinary_deep_parent_from_raw_hub_prior
    (P Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (Z:Finset U)
    (π:Equiv.Perm V) (d k:ℕ) (j:Color) (s:U→Color→ℝ)
    (weight:V→Sym2 (V⊕U)→ℝ) (triangleWeight:OrdinaryCycle P 3→ℝ)
    (γ κ b B εf η κe p pR pH density tR tH L Ledit βe βh δ ε t Kscale e:ℝ)
    (α pstar βP ηP ηH βH c Btri:ℝ) (σ:RawWheelOutcome V U Γ Color)
    (margins:OrdinaryDeepParentMargins P F A Z γ κ b B εf η κe p pR pH density tR tH L Ledit δ ε t Kscale e)
    (hQ:Q≤P\F)
    (profile:OrdinaryCleanupParentProfiles P Q F H π d A Z pR pH density tR tH Ledit βe βh s j σ)
    (parent:EndpointPhysicalParentWeights P A Aᶜ weight)
    (event:OrdinaryRawHubParentPrior d k P F A Z π j s weight triangleWeight
      α pstar βP ηP ηH βH c Btri pR pH t tR tH σ)
    (hw:OrdinaryMixedHubWeights b B η Q F H A Z) :
    MixedFreshParentDataInsideRoots γ κ b B εf η (spanningRestriction Q A) F
      (ordinaryPhysicalGraph (spanningRestriction Q A) (fun v u=>H v u∧v∈A∧u∈Z))
      (ordinaryPhysicalGraph F (fun _ _=>False)) (Function.Embedding.inl:V↪V⊕U)
      (ordinaryBoundaryHubSet H Z A) (fun i=>(ordinaryBoundaryRimSet Q A i).image Sum.inl)
      (fun i=>(ordinaryBoundaryRowSet H A Z i).image Sum.inr) := by
  have inputs:=ordinary_deep_ingredients_from_raw_hub_prior P Q F H A Z π d k j s weight triangleWeight
    γ κ b B εf η κe p pR pH density tR tH L Ledit βe βh δ ε t Kscale e
    α pstar βP ηP ηH βH c Btri σ margins hQ profile parent event
  exact ordinary_deep_parent_from_ingredients P Q F H A Z π d j s weight
    γ κ b B εf η κe p pR pH density tR tH L Ledit βe βh δ ε t Kscale σ inputs hw
end Oberwolfach
