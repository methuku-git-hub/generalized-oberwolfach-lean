module

public import Oberwolfach.OrdinaryMixedParentFromDeepSampleInside

@[expose] public section
/-! The explicit non-hub inputs for the corrected mixed parent on one raw
outcome, collected without changing their hypotheses or quantifier order. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

structure OrdinaryDeepParentIngredients
    (P Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (Z:Finset U)
    (π:Equiv.Perm V) (d:ℕ) (j:Color) (s:U→Color→ℝ) (weight:V→Sym2 (V⊕U)→ℝ)
    (γ κ b B εf η κe p pR pH density tR tH L Ledit βe βh δ ε t K:ℝ)
    (σ:RawWheelOutcome V U Γ Color) : Prop where
  profile : OrdinaryCleanupParentProfiles P Q F H π d A Z pR pH density tR tH Ledit βe βh s j σ
  deep : RawOrdinaryRows P π d 3 A pR s j tR σ
  parent : EndpointPhysicalParentWeights P A Aᶜ weight
  endpoint_event : EndpointPhysicalPotentialEvent P F A Z Aᶜ π d j weight pR pH t σ
  geom : EndpointPhysicalEditedConditions P Q F H A Z Aᶜ π d j κe p pR pH L Ledit δ σ
  density_lower : (3/4:ℝ)≤density
  conflict_degree : ∀v,(F.degree v:ℝ)≤L
  epsilon_nonneg : 0≤εf
  conflict_scale : L≤εf*Fintype.card V
  conflict_inner : L≤(A.card:ℝ)/24
  row_margin : tR+4*Ledit≤ε*A.card
  index_margin : tH+3*Ledit≤ε*Z.card
  count_error : ε≤min (p^4/16) (p^3/2)
  hub_scale : γ*Fintype.card V≤(p^4/16)*A.card
  pair_scale : κ*Fintype.card V≤(p^4/16)*A.card
  endpoint_scale : γ*Fintype.card (V⊕U)≤endpointCountCoefficient p κe*A.card
  parent_degree : ∀x∉A,∀v∈insert x A,(3/4:ℝ)*A.card≤((A∩P.neighborFinset v).card:ℝ)
  scale_nonneg : 0≤K
  physical_scale : (Fintype.card (V⊕U):ℝ)≤K*A.card
  endpoint_error : δ+(2*40+(1+2*40)/(2*κe*p))*L/A.card+(t+10*(40/(κe*p^5))*Ledit/A.card)≤η
  lower_bound : b≤1/30
  upper_bound : (40/(κe*p^5))*K^2≤B
end Oberwolfach
