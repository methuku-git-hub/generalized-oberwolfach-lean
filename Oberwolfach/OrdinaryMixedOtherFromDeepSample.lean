module

public import Oberwolfach.OrdinaryMixedHubWeights
public import Oberwolfach.EndpointNeighborhoodsFromCleanup
public import Oberwolfach.OrdinaryHubConditionsFromDeepSample

@[expose] public section
/-! All non-weight fields of the corrected mixed-factor parent follow from
the deeper sample, cleanup edits and explicit size/error margins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
set_option synthInstance.maxSize 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

def ordinary_mixed_other_from_deep_sample
    (P Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (Z:Finset U)
    (π:Equiv.Perm V) (d:ℕ) (j:Color) (s:U→Color→ℝ)
    (γ κ b B εf η κe p pR pH density tR tH L Ledit βe βh δ ε:ℝ) (σ:RawWheelOutcome V U Γ Color)
    (profile:OrdinaryCleanupParentProfiles P Q F H π d A Z pR pH density tR tH Ledit βe βh s j σ)
    (deep:RawOrdinaryRows P π d 3 A pR s j tR σ)
    (geom:EndpointPhysicalEditedConditions P Q F H A Z Aᶜ π d j κe p pR pH L Ledit δ σ)
    (hw:OrdinaryMixedHubWeights b B η Q F H A Z)
    (hdensity:(3/4:ℝ)≤density) (hF:∀v,(F.degree v:ℝ)≤L) (hεf:0≤εf)
    (hFscale:L≤εf*Fintype.card V) (hLA:L≤(A.card:ℝ)/24)
    (hrow:tR+4*Ledit≤ε*A.card) (hindex:tH+3*Ledit≤ε*Z.card)
    (hε:ε≤min (p^4/16) (p^3/2))
    (hγscale:γ*Fintype.card V≤(p^4/16)*A.card)
    (hκscale:κ*Fintype.card V≤(p^4/16)*A.card)
    (hendpointscale:γ*Fintype.card (V⊕U)≤endpointCountCoefficient p κe*A.card)
    (hdeg:∀x∉A,∀v∈insert x A,(3/4:ℝ)*A.card≤((A∩P.neighborFinset v).card:ℝ)):
    OrdinaryMixedOtherParentInputsInside γ κ b B εf η Q F H A Z:=by
  have hh:=ordinary_hub_conditions_from_deep_sample P Q F H A Z π d j s γ κ p pR pH density tR tH L Ledit βe βh ε σ
    profile deep geom.p_pos (geom.rim_lower.trans geom.rim_upper) geom.rim_lower geom.spoke_lower hdensity
    geom.conflict_nonneg geom.edit_nonneg hLA hF hrow (hε.trans (min_le_left _ _)) hγscale hκscale
  have he:=endpoint_neighborhoods_from_cleanup P Q F H A Z π d j s γ κe p pR pH density tR tH L Ledit βe βh δ ε σ
    profile deep geom hrow hindex hLA hε hendpointscale hdeg
  have hVW:(Fintype.card V:ℝ)≤Fintype.card (V⊕U):=by
    exact_mod_cast Fintype.card_le_of_injective Sum.inl Sum.inl_injective
  refine
    { hub_size := hh.1
      rim_conflict := fun v=>(hF v).trans hFscale
      physical_conflict := ?_
      hub_neighborhoods := hh.2
      endpoint_neighborhoods := he
      hub_weight := hw.weight
      hub_weight_bounds := hw.bounds
      hub_weight_load := hw.loads }
  intro v
  exact (geom.conflict_degree v).trans (hFscale.trans (mul_le_mul_of_nonneg_left hVW hεf))
end Oberwolfach
