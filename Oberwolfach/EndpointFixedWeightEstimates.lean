module

public import Oberwolfach.EndpointPotentialLoads
public import Oberwolfach.EndpointWeightNormalization

@[expose] public section

/-! The actual triangle weights, with the fixed parent matching and the
root-omitted potentials of the manuscript. All losses use the original
row-domain cardinality. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem endpoint_fixed_weight_estimates
    (P R H F : SimpleGraph V) (A B : Finset V) (x : V)
    (hAB : Disjoint A B) (hR : R≤P\F)
    (hFB : ∀ u∈B,∀ w,¬F.Adj u w)
    (κ p q s c C L δ ξ : ℝ)
    (ha : 0<(A.card:ℝ)) (hκ : 0<κ) (hp : 0<p)
    (hc : 0≤c) (hC : 0≤C) (hL : 0≤L) (hδ : 0≤δ)
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
      |endpointRowPotential P R H F A B x v weight (B.card*q^2*s^3)-
        endpointEligibleRowWeight F (A∩P.neighborFinset x) x v (fun v w=>weight s(v,w))|≤ξ)
    (hindex : ∀ u∈B,
      |endpointIndexPotential P R H F A x u weight (B.card*q^2*s^3)-
        q/(B.card*s)*(∑ e∈(endpointEligibleGraph P F (A∩P.neighborFinset x) x).edgeFinset,weight e)|≤ξ) :
    let S:=common A {x} (fun y=>R.neighborFinset y)
    let T:=common B {x} (fun y=>H.neighborFinset y)
    let wt:=fun D : EndpointTriangle (endpointHostGraph R H A B) F S T=>
      weight (endpointTriangleRowEdge D)/(B.card*q^2*s^3)
    (∀ D,c/(A.card:ℝ)^2≤wt D ∧ wt D≤(C/(κ*p^5))/(A.card:ℝ)^2) ∧
    (∀ v∈S∪T,|1-hypergraphWeightedDegree endpointTriangleVertices wt v|≤
      δ+(2*C+(1+2*C)/(2*κ*p))*L/A.card+ξ) := by
  dsimp only
  let Px:=A∩P.neighborFinset x
  have hPa : (Px.card:ℝ)≤A.card := by exact_mod_cast Finset.card_le_card Finset.inter_subset_left
  have hmass:=endpoint_unordered_matching_mass_error P F Px x weight A.card C L ha hC hPa hF hweight hsum hzero
  have hindexTarget:=endpoint_index_target_error (A.card:ℝ) B.card κ p q s C L Px.card
    (∑ e∈(endpointEligibleGraph P F Px x).edgeFinset,weight e) δ
    ha hκ hp hC hL hb (hp.le.trans hq) hq1 hs hmass hbalance
  have hrowLoss : 2*C*L/A.card≤(2*C+(1+2*C)/(2*κ*p))*L/A.card := by
    apply div_le_div_of_nonneg_right _ ha.le
    apply mul_le_mul_of_nonneg_right _ hL
    have : 0≤(1+2*C)/(2*κ*p) := by positivity
    linarith
  have hindexLoss : ((1+2*C)/(2*κ*p))*L/A.card≤(2*C+(1+2*C)/(2*κ*p))*L/A.card := by
    apply div_le_div_of_nonneg_right _ ha.le
    apply mul_le_mul_of_nonneg_right _ hL
    linarith
  constructor
  · intro D
    exact endpoint_triangle_coefficient_bounds A.card B.card κ p q s c C _ ha hκ hp hc hC hb
      (by exact_mod_cast hba) hq hq1 hs hs1
      (hpositive _ (endpoint_triangle_parent_edge P R H F A B x hAB hR hFB D))
  · intro v hv
    rcases Finset.mem_union.mp hv with hv|hv
    · have hv' := (mem_singleton_common_graph R A x v).mp hv
      have hvP : v∈Px := Finset.mem_inter.mpr ⟨hv'.1,by simpa using (hR hv'.2).1⟩
      have hvE:= (mem_singleton_common_graph (P\F) A x v).mpr ⟨hv'.1,hR hv'.2⟩
      have htarget:=endpoint_matching_row_target F Px x v (fun v w=>weight s(v,w)) A.card C L
        ha hC hF (hweight v hvP) (hsum v hvP)
      rw [endpoint_row_potential_present P R H F A B x v hAB hR hFB hv weight _]
      rw [abs_sub_comm]
      have hh:=abs_sub_le (endpointRowPotential P R H F A B x v weight (B.card*q^2*s^3))
        (endpointEligibleRowWeight F Px x v (fun v w=>weight s(v,w))) 1
      have hrow' := hrow v (by convert hvE using 1 <;> congr!)
      linarith only [hh,hrow',htarget,hrowLoss,hδ]
    · have hvB := ((mem_singleton_common_graph H B x v).mp hv).1
      rw [endpoint_index_potential_present P R H F A B x v hAB hR hFB hv weight _]
      rw [abs_sub_comm]
      have hh:=abs_sub_le (endpointIndexPotential P R H F A x v weight (B.card*q^2*s^3))
        (q/(B.card*s)*(∑ e∈(endpointEligibleGraph P F Px x).edgeFinset,weight e)) 1
      linarith only [hh,hindex v hvB,hindexTarget,hindexLoss]

end Oberwolfach
