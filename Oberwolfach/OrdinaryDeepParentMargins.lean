module

public import Oberwolfach.OrdinaryDeepParentIngredients
public import Oberwolfach.EndpointConditionsFromCleanupProfile

@[expose] public section
/-! Deterministic size, balance and conflict margins for constructing the
deep/endpoint parent ingredients from an actual cleanup profile. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

structure OrdinaryDeepParentMargins
    (P F:SimpleGraph V) (A:Finset V) (Z:Finset U)
    (γ κ b B εf η κe p pR pH density tR tH L Ledit δ ε t K e:ℝ) : Prop where
  Apos : 0<A.card
  kappa_pos : 0<κe
  p_pos : 0<p
  conflict_nonneg : 0≤L
  edit_nonneg : 0≤Ledit
  delta_nonneg : 0≤δ
  hub_lower : κe*A.card≤(Z.card:ℝ)
  hub_upper : Z.card≤A.card
  rim_lower : p≤pR
  rim_upper : pR≤1
  spoke_lower : p≤pH
  spoke_upper : pH≤1
  conflict_degree : ∀v,(F.degree v:ℝ)≤L
  parent_balance : ∀v,|pR*(A∩P.neighborFinset v).card-2*pH*Z.card|≤e
  balance_margin : e≤δ*(2*Z.card*pH)
  density_lower : (3/4:ℝ)≤density
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
