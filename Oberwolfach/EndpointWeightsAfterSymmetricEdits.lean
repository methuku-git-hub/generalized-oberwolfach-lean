module

public import Oberwolfach.EndpointPotentialFromSymmetricEdits
public import Oberwolfach.EndpointFixedWeightEstimates
public import Oberwolfach.EndpointNormalizedParentWeights

@[expose] public section
/-! Fixed parent matching weights remain valid after bounded symmetric edits,
including newly added edges, with an explicit potential error. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem endpoint_fixed_weights_after_symmetric_edits
    (P R₀ R H₀ H F : SimpleGraph V) (A B : Finset V) (x : V)
    (hAB : Disjoint A B) (hR : R ≤ P\F)
    (hFB : ∀ u∈B, ∀ w, ¬F.Adj u w)
    (κ p q s c C L Ledit δ ξ : ℝ)
    (ha : 0<(A.card:ℝ)) (hκ : 0<κ) (hp : 0<p)
    (hc : 0≤c) (hC : 0≤C) (hL : 0≤L) (hLedit : 0≤Ledit) (hδ : 0≤δ)
    (hb : κ*A.card≤(B.card:ℝ)) (hba : B.card≤A.card)
    (hq : p≤q) (hq1 : q≤1) (hs : p≤s) (hs1 : s≤1)
    (hF : ∀ u,(F.degree u:ℝ)≤L)
    (weight : Sym2 V→ℝ)
    (hweight : ∀ v∈A∩P.neighborFinset x,∀ w∈A∩P.neighborFinset x,
      0≤weight s(v,w) ∧ weight s(v,w)≤C/A.card)
    (hsum : ∀ v∈A∩P.neighborFinset x,
      ∑ w∈A∩P.neighborFinset x,weight s(v,w)=1)
    (hzero : ∀ v∈A∩P.neighborFinset x,∀ w∈A∩P.neighborFinset x,
      ¬P.Adj v w → weight s(v,w)=0)
    (hpositive : ∀ e∈(endpointEligibleGraph P F (A∩P.neighborFinset x) x).edgeSet,
      c/A.card≤weight e ∧ weight e≤C/A.card)
    (hbalance : |q*(A∩P.neighborFinset x).card/(2*B.card*s)-1|≤δ)
    (hrow : ∀ v∈common A {x} (fun y=>(P\F).neighborFinset y),
      |endpointRowPotential P R₀ H₀ F A B x v weight (B.card*q^2*s^3)-
        endpointEligibleRowWeight F (A∩P.neighborFinset x) x v (fun v w=>weight s(v,w))|≤ξ)
    (hindex : ∀ u∈B,
      |endpointIndexPotential P R₀ H₀ F A x u weight (B.card*q^2*s^3)-
        q/(B.card*s)*(∑ e∈(endpointEligibleGraph P F (A∩P.neighborFinset x) x).edgeFinset,weight e)|≤ξ)
    (heditR : ∀v,((changed (R₀.neighborFinset v) (R.neighborFinset v)).card:ℝ)≤Ledit)
    (heditH : ∀v,((changed (H₀.neighborFinset v) (H.neighborFinset v)).card:ℝ)≤Ledit) :
    let S:=common A {x} (fun y=>R.neighborFinset y)
    let T:=common B {x} (fun y=>H.neighborFinset y)
    let wt:=fun D : EndpointTriangle (endpointHostGraph R H A B) F S T=>
      weight (endpointTriangleRowEdge D)/(B.card*q^2*s^3)
    (∀ D,c/(A.card:ℝ)^2≤wt D ∧ wt D≤(C/(κ*p^5))/(A.card:ℝ)^2) ∧
    (∀ v∈S∪T,|1-hypergraphWeightedDegree endpointTriangleVertices wt v|≤
      δ+(2*C+(1+2*C)/(2*κ*p))*L/A.card+(ξ+10*(C/(κ*p^5))*Ledit/A.card)) := by
  let Cedit:=C/(κ*p^5)
  have hCedit:0≤Cedit:=by dsimp [Cedit]; positivity
  have hnormal:=endpoint_normalized_parent_weight_bounds P F A B x weight κ p q s c C
    ha hκ hp hc hC hb hba hq hq1 hs hs1 hpositive
  have hAN : 0<A.card := by exact_mod_cast ha
  have hdiff:
      (∀v,|endpointRowPotential P R H F A B x v weight (B.card*q^2*s^3)-
        endpointRowPotential P R₀ H₀ F A B x v weight (B.card*q^2*s^3)|≤10*Cedit*Ledit/A.card) ∧
      (∀u,|endpointIndexPotential P R H F A x u weight (B.card*q^2*s^3)-
        endpointIndexPotential P R₀ H₀ F A x u weight (B.card*q^2*s^3)|≤6*Cedit*Ledit/A.card) := by
    apply endpoint_potential_from_symmetric_edits P R₀ R H₀ H F A B x weight
      (B.card*q^2*s^3) Cedit Ledit hAN hba hCedit hLedit
    · exact hnormal
    · exact heditR
    · exact heditH
  have hrow' : ∀ v∈common A {x} (fun y=>(P\F).neighborFinset y),
      |endpointRowPotential P R H F A B x v weight (B.card*q^2*s^3)-
        endpointEligibleRowWeight F (A∩P.neighborFinset x) x v (fun v w=>weight s(v,w))|
        ≤ξ+10*Cedit*Ledit/A.card := by
    intro v hv
    have ht:=abs_sub_le (endpointRowPotential P R H F A B x v weight (B.card*q^2*s^3))
      (endpointRowPotential P R₀ H₀ F A B x v weight (B.card*q^2*s^3))
      (endpointEligibleRowWeight F (A∩P.neighborFinset x) x v (fun v w=>weight s(v,w)))
    linarith [hdiff.1 v, hrow v hv]
  have hloss : 6*Cedit*Ledit/A.card ≤ 10*Cedit*Ledit/A.card := by
    apply div_le_div_of_nonneg_right _ ha.le
    nlinarith [mul_nonneg hCedit hLedit]
  have hindex' : ∀ u∈B,
      |endpointIndexPotential P R H F A x u weight (B.card*q^2*s^3)-
        q/(B.card*s)*(∑ e∈(endpointEligibleGraph P F (A∩P.neighborFinset x) x).edgeFinset,weight e)|
        ≤ξ+10*Cedit*Ledit/A.card := by
    intro u hu
    have ht:=abs_sub_le (endpointIndexPotential P R H F A x u weight (B.card*q^2*s^3))
      (endpointIndexPotential P R₀ H₀ F A x u weight (B.card*q^2*s^3))
      (q/(B.card*s)*(∑ e∈(endpointEligibleGraph P F (A∩P.neighborFinset x) x).edgeFinset,weight e))
    linarith [hdiff.2 u, hindex u hu]
  exact endpoint_fixed_weight_estimates P R H F A B x hAB hR hFB κ p q s c C L δ
    (ξ+10*Cedit*Ledit/A.card) ha hκ hp hc hC hL hδ hb hba hq hq1 hs hs1 hF weight
    hweight hsum hzero hpositive hbalance hrow' hindex'
end Oberwolfach
