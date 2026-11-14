module

public import Oberwolfach.OrdinaryMixedParentFromEndpointWeightsInside
public import Oberwolfach.EndpointConditionsFromCleanupProfile

@[expose] public section
/-! Build the mixed-factor parent from the fixed endpoint event and the
actual cleanup profile on the same sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
set_option synthInstance.maxSize 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

def ordinary_mixed_parent_from_cleanup_inside
    (P Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (Z:Finset U)
    (π:Equiv.Perm V) (d:ℕ) (j:Color) (s:U→Color→ℝ) (weight:V→Sym2 (V⊕U)→ℝ)
    (γ κ b B ε η κe p pR pH density tR tH L Ledit βe βh δ e t K:ℝ)
    (σ:RawWheelOutcome V U Γ Color)
    (profile:OrdinaryCleanupParentProfiles P Q F H π d A Z pR pH density tR tH Ledit βe βh s j σ)
    (parent:EndpointPhysicalParentWeights P A Aᶜ weight)
    (event:EndpointPhysicalPotentialEvent P F A Z Aᶜ π d j weight pR pH t σ)
    (hA:0<A.card) (hQ:Q≤P\F) (hκe:0<κe) (hp:0<p) (hL:0≤L) (hLedit:0≤Ledit) (hδ:0≤δ)
    (hZ:κe*A.card≤(Z.card:ℝ)) (hZA:Z.card≤A.card)
    (hpR:p≤pR) (hpR1:pR≤1) (hpH:p≤pH) (hpH1:pH≤1)
    (hF:∀v,(F.degree v:ℝ)≤L)
    (hparent:∀v,|pR*(A∩P.neighborFinset v).card-2*pH*Z.card|≤e)
    (hmargin:e≤δ*(2*Z.card*pH))
    (hK:0≤K) (hsize:(Fintype.card (V⊕U):ℝ)≤K*A.card)
    (herr:δ+(2*40+(1+2*40)/(2*κe*p))*L/A.card+(t+10*(40/(κe*p^5))*Ledit/A.card)≤η)
    (hb:b≤1/30) (hB:(40/(κe*p^5))*K^2≤B)
    (other:OrdinaryMixedOtherParentInputsInside γ κ b B ε η Q F H A Z):
    MixedFreshParentDataInsideRoots γ κ b B ε η (spanningRestriction Q A) F
      (ordinaryPhysicalGraph (spanningRestriction Q A) (fun v u=>H v u∧v∈A∧u∈Z))
      (ordinaryPhysicalGraph F (fun _ _=>False)) (Function.Embedding.inl:V↪V⊕U)
      (ordinaryBoundaryHubSet H Z A) (fun i=>(ordinaryBoundaryRimSet Q A i).image Sum.inl)
      (fun i=>(ordinaryBoundaryRowSet H A Z i).image Sum.inr):=by
  have geom:=endpoint_conditions_from_cleanup_profile P Q F H A Z π d j s κe p pR pH density tR tH L Ledit
    βe βh δ e σ profile hA hQ hκe hp hL hLedit hδ hZ hZA hpR hpR1 hpH hpH1 hF hparent hmargin
  exact ordinary_mixed_parent_from_endpoint_weights_inside P Q F H A Z π d j weight γ κ b B ε η κe p pR pH L Ledit δ t K σ
    parent event geom hK hsize herr hb hB other
end Oberwolfach
