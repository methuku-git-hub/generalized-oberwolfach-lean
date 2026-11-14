module

public import Oberwolfach.EndpointPotentialLoads
public import Oberwolfach.InducedFractionalCycles

@[expose] public section

/-! Restrict the sampling conflict graph to the rim vertices before using
an endpoint factor on a graph with separate hub vertices. Eligible edges,
root domains, fixed targets and potential sums are unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type*} [Fintype V] [DecidableEq V]

theorem endpoint_eligible_graph_conflict_restriction (P F:SimpleGraph V) (S Y:Finset V) (x:V)
    (hS:S⊆Y) (hx:x∈Y):
    endpointEligibleGraph P (spanningRestriction F Y) S x=endpointEligibleGraph P F S x:=by
  ext v w
  by_cases hv:v∈S <;> by_cases hw:w∈S
  · simp only [endpointEligibleGraph,spanningRestriction_adj,hv,hw,hS hv,hS hw,hx,and_true,true_and]
  · simp [endpointEligibleGraph,hw]
  · simp [endpointEligibleGraph,hv]
  · simp [endpointEligibleGraph,hv]

theorem endpoint_row_target_conflict_restriction (F:SimpleGraph V) (S Y:Finset V) (x v:V)
    (hS:S⊆Y) (hx:x∈Y) (hv:v∈Y) (w:V→V→ℝ):
    endpointEligibleRowWeight (spanningRestriction F Y) S x v w=endpointEligibleRowWeight F S x v w:=by
  unfold endpointEligibleRowWeight
  apply Finset.sum_congr rfl
  intro z hz
  simp only [spanningRestriction_adj,hx,hv,hS hz,and_true]

theorem endpoint_potentials_conflict_restriction (P R H F:SimpleGraph V) (A B Y:Finset V)
    (x:V) (hA:A⊆Y) (hx:x∈Y) (weight:Sym2 V→ℝ) (D:ℝ):
    (∀ v,endpointRowPotential P R H (spanningRestriction F Y) A B x v weight D=
      endpointRowPotential P R H F A B x v weight D) ∧
    (∀ u,endpointIndexPotential P R H (spanningRestriction F Y) A x u weight D=
      endpointIndexPotential P R H F A x u weight D):=by
  have he:=endpoint_eligible_graph_conflict_restriction P F (A∩P.neighborFinset x) Y x
    (Finset.inter_subset_left.trans hA) hx
  constructor
  · intro v
    simp only [endpointRowPotential,EndpointRowPotentialPredicate,he]
    congr!
  · intro u
    simp only [endpointIndexPotential,EndpointIndexPotentialPredicate,he]
    congr!

theorem common_conflict_restriction (P F:SimpleGraph V) (A S Y:Finset V)
    (hA:A⊆Y) (hS:S⊆Y):
    common A S (fun v=>(P\spanningRestriction F Y).neighborFinset v)=
      common A S (fun v=>(P\F).neighborFinset v):=by
  ext z
  simp only [mem_common_iff,SimpleGraph.mem_neighborFinset,SimpleGraph.sdiff_adj,spanningRestriction_adj]
  constructor
  · rintro ⟨hz,h⟩
    exact ⟨hz,fun v hv=>⟨(h v hv).1,fun hf=>(h v hv).2 ⟨hf,hS hv,hA hz⟩⟩⟩
  · rintro ⟨hz,h⟩
    exact ⟨hz,fun v hv=>⟨(h v hv).1,fun hf=>(h v hv).2 hf.1⟩⟩

theorem restricted_conflict_has_no_hub_edges (F:SimpleGraph V) (Y B:Finset V) (hYB:Disjoint Y B):
    ∀ u∈B,∀ v,¬(spanningRestriction F Y).Adj u v:=by
  intro u hu v h
  exact Finset.disjoint_left.mp hYB ((spanningRestriction_adj F Y u v).mp h).2.1 hu

end Oberwolfach
