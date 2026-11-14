module

public import Oberwolfach.EndpointWeightsAfterSymmetricEdits

@[expose] public section
/-! Conditions on a later sampled and edited host, with the parent matching
weight fixed before that sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

structure EndpointParentWeightSampleInputs
    (P R₀ R H₀ H F:SimpleGraph V) (A B:Finset V) (x:V) (weight:Sym2 V→ℝ)
    (κ p q s L Ledit δ ξ:ℝ):Prop where
  disjoint:Disjoint A B
  rim_sub:R≤P\F
  conflict_free_index:∀u∈B,∀w,¬F.Adj u w
  kappa_pos:0<κ
  p_pos:0<p
  conflict_nonneg:0≤L
  edit_nonneg:0≤Ledit
  balance_nonneg:0≤δ
  index_lower:κ*A.card≤(B.card:ℝ)
  index_upper:B.card≤A.card
  rim_lower:p≤q
  rim_upper:q≤1
  spoke_lower:p≤s
  spoke_upper:s≤1
  conflict_degree:∀u,(F.degree u:ℝ)≤L
  parent_balance:|q*(A∩P.neighborFinset x).card/(2*B.card*s)-1|≤δ
  row_potential:∀v∈common A {x} (fun y=>(P\F).neighborFinset y),
    |endpointRowPotential P R₀ H₀ F A B x v weight (B.card*q^2*s^3)-
      endpointEligibleRowWeight F (A∩P.neighborFinset x) x v (fun v w=>weight s(v,w))|≤ξ
  index_potential:∀u∈B,
    |endpointIndexPotential P R₀ H₀ F A x u weight (B.card*q^2*s^3)-
      q/(B.card*s)*(∑e∈(endpointEligibleGraph P F (A∩P.neighborFinset x) x).edgeFinset,weight e)|≤ξ
  rim_edit:∀v,((changed (R₀.neighborFinset v) (R.neighborFinset v)).card:ℝ)≤Ledit
  spoke_edit:∀v,((changed (H₀.neighborFinset v) (H.neighborFinset v)).card:ℝ)≤Ledit

def EndpointParentWeightSampleConclusion
    (R H F:SimpleGraph V) (A B:Finset V) (x:V) (weight:Sym2 V→ℝ)
    (κ p q s L Ledit δ ξ:ℝ):Prop :=
  let S:=common A {x} (fun y=>R.neighborFinset y)
  let T:=common B {x} (fun y=>H.neighborFinset y)
  let wt:=fun D:EndpointTriangle (endpointHostGraph R H A B) F S T=>
    weight (endpointTriangleRowEdge D)/(B.card*q^2*s^3)
  (∀D,(1/30:ℝ)/(A.card:ℝ)^2≤wt D ∧ wt D≤(40/(κ*p^5))/(A.card:ℝ)^2) ∧
  (∀v∈S∪T,|1-hypergraphWeightedDegree endpointTriangleVertices wt v|≤
    δ+(2*40+(1+2*40)/(2*κ*p))*L/A.card+(ξ+10*(40/(κ*p^5))*Ledit/A.card))
end Oberwolfach
