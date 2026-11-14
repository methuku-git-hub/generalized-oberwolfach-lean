module

public import Oberwolfach.OrdinaryTriangleHubWeightsFromLength
public import Oberwolfach.OrdinaryDeepIngredientsFromCommon
public import Oberwolfach.OrdinaryDeepParentFromIngredients

@[expose] public section
/-! The common endpoint and row tests plus the actual length-two hub weights
construct the triangle fresh-factor parent on the same corrected host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 12000000
set_option synthInstance.maxSize 8192
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

def ordinary_triangle_parent_from_common_length_weights
    (P Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (Z:Finset U)
    (π:Equiv.Perm V) (d:ℕ) (j:Color) (s:U→Color→ℝ) (weight:V→Sym2 (V⊕U)→ℝ)
    (γ κ b B εf η κe p pR pH density tR tH L Ledit βe βh δ ε t K e:ℝ)
    (σ:RawWheelOutcome V U Γ Color)
    (margins:OrdinaryDeepParentMargins P F A Z γ κ b B εf η κe p pR pH density tR tH L Ledit δ ε t K e)
    (hQ:Q≤P\F)
    (profile:OrdinaryCleanupParentProfiles P Q F H π d A Z pR pH density tR tH Ledit βe βh s j σ)
    (deep:RawOrdinaryRows P π d 3 A pR s j tR σ)
    (parent:EndpointPhysicalParentWeights P A Aᶜ weight)
    (event:EndpointPhysicalPotentialEvent P F A Z Aᶜ π d j weight pR pH t σ)
    (hw:OrdinaryMixedHubWeightsOfLength 2 b B η Q F H A Z):
    MixedFreshParentDataInsideRoots γ κ b B εf η (spanningRestriction Q A) F
      (ordinaryPhysicalGraph (spanningRestriction Q A) (fun v u=>H v u∧v∈A∧u∈Z))
      (ordinaryPhysicalGraph F (fun _ _=>False)) (Function.Embedding.inl:V↪V⊕U)
      (ordinaryBoundaryHubSet H Z A) (fun i=>(ordinaryBoundaryRimSet Q A i).image Sum.inl)
      (fun i=>(ordinaryBoundaryRowSet H A Z i).image Sum.inr) :=by
  have hi:=ordinary_deep_ingredients_from_common P Q F H A Z π d j s weight
    γ κ b B εf η κe p pR pH density tR tH L Ledit βe βh δ ε t K e σ margins hQ profile deep parent event
  exact ordinary_deep_parent_from_ingredients P Q F H A Z π d j s weight
    γ κ b B εf η κe p pR pH density tR tH L Ledit βe βh δ ε t K σ hi
      (ordinary_triangle_hub_weights_from_length Q F H A Z b B η hw)
end Oberwolfach
