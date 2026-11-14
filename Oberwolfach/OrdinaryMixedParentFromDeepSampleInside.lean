module

public import Oberwolfach.OrdinaryMixedOtherFromDeepSample
public import Oberwolfach.OrdinaryMixedParentFromEndpointWeightsInside

@[expose] public section
/-! On one sample, the deeper counts and endpoint parent weights supply the
corrected mixed-factor parent, leaving only hub cycle weights explicit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
set_option synthInstance.maxSize 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

def ordinary_mixed_parent_from_deep_sample_inside
    (P Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (Z:Finset U)
    (π:Equiv.Perm V) (d:ℕ) (j:Color) (s:U→Color→ℝ) (weight:V→Sym2 (V⊕U)→ℝ)
    (γ κ b B εf η κe p pR pH density tR tH L Ledit βe βh δ ε t K:ℝ)
    (σ:RawWheelOutcome V U Γ Color)
    (profile:OrdinaryCleanupParentProfiles P Q F H π d A Z pR pH density tR tH Ledit βe βh s j σ)
    (deep:RawOrdinaryRows P π d 3 A pR s j tR σ)
    (parent:EndpointPhysicalParentWeights P A Aᶜ weight)
    (event:EndpointPhysicalPotentialEvent P F A Z Aᶜ π d j weight pR pH t σ)
    (geom:EndpointPhysicalEditedConditions P Q F H A Z Aᶜ π d j κe p pR pH L Ledit δ σ)
    (hw:OrdinaryMixedHubWeights b B η Q F H A Z)
    (hdensity:(3/4:ℝ)≤density) (hF:∀v,(F.degree v:ℝ)≤L) (hεf:0≤εf)
    (hFscale:L≤εf*Fintype.card V) (hLA:L≤(A.card:ℝ)/24)
    (hrow:tR+4*Ledit≤ε*A.card) (hindex:tH+3*Ledit≤ε*Z.card)
    (hε:ε≤min (p^4/16) (p^3/2))
    (hγscale:γ*Fintype.card V≤(p^4/16)*A.card)
    (hκscale:κ*Fintype.card V≤(p^4/16)*A.card)
    (hendpointscale:γ*Fintype.card (V⊕U)≤endpointCountCoefficient p κe*A.card)
    (hdeg:∀x∉A,∀v∈insert x A,(3/4:ℝ)*A.card≤((A∩P.neighborFinset v).card:ℝ))
    (hK:0≤K) (hsize:(Fintype.card (V⊕U):ℝ)≤K*A.card)
    (herr:δ+(2*40+(1+2*40)/(2*κe*p))*L/A.card+(t+10*(40/(κe*p^5))*Ledit/A.card)≤η)
    (hb:b≤1/30) (hB:(40/(κe*p^5))*K^2≤B):
    MixedFreshParentDataInsideRoots γ κ b B εf η (spanningRestriction Q A) F
      (ordinaryPhysicalGraph (spanningRestriction Q A) (fun v u=>H v u∧v∈A∧u∈Z))
      (ordinaryPhysicalGraph F (fun _ _=>False)) (Function.Embedding.inl:V↪V⊕U)
      (ordinaryBoundaryHubSet H Z A) (fun i=>(ordinaryBoundaryRimSet Q A i).image Sum.inl)
      (fun i=>(ordinaryBoundaryRowSet H A Z i).image Sum.inr):=by
  have other:=ordinary_mixed_other_from_deep_sample P Q F H A Z π d j s γ κ b B εf η κe p pR pH density
    tR tH L Ledit βe βh δ ε σ profile deep geom hw hdensity hF hεf hFscale hLA hrow hindex hε
    hγscale hκscale hendpointscale hdeg
  exact ordinary_mixed_parent_from_endpoint_weights_inside P Q F H A Z π d j weight γ κ b B εf η κe p pR pH
    L Ledit δ t K σ parent event geom hK hsize herr hb hB other
end Oberwolfach
