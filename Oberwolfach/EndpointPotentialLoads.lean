module

public import Oberwolfach.EndpointPotentialPredicates

@[expose] public section

/-! At a present root the fixed potential sum is exactly the incident
sum in the actual endpoint-triangle family. Absent root states are not
required to define either potential. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

def endpointRowPotential (P R H F : SimpleGraph V) (A B : Finset V)
    (x v : V) (weight : Sym2 V→ℝ) (d : ℝ) : ℝ :=
  ∑ p : V×V,if EndpointRowPotentialPredicate P R H F A B x v p then weight s(v,p.2)/d else 0

def endpointIndexPotential (P R H F : SimpleGraph V) (A : Finset V)
    (x u : V) (weight : Sym2 V→ℝ) (d : ℝ) : ℝ :=
  ∑ edge : Sym2 V,if EndpointIndexPotentialPredicate P R H F A x u edge then weight edge/d else 0

theorem endpoint_row_potential_present (P R H F : SimpleGraph V) (A B : Finset V)
    (x v : V) (hAB : Disjoint A B) (hR : R≤P\F)
    (hFB : ∀ u∈B,∀ w,¬F.Adj u w)
    (hv : v∈common A {x} (fun y=>R.neighborFinset y)) (weight : Sym2 V→ℝ) (d : ℝ) :
    hypergraphWeightedDegree endpointTriangleVertices
      (fun C : EndpointTriangle (endpointHostGraph R H A B) F
        (common A {x} (fun y=>R.neighborFinset y)) (common B {x} (fun y=>H.neighborFinset y))=>
          weight (endpointTriangleRowEdge C)/d) v = endpointRowPotential P R H F A B x v weight d := by
  have hST : Disjoint (common A {x} (fun y=>R.neighborFinset y)) (common B {x} (fun y=>H.neighborFinset y)) :=
    hAB.mono (fun z hz=>((mem_singleton_common_graph R A x z).mp hz).1)
      (fun z hz=>((mem_singleton_common_graph H B x z).mp hz).1)
  have hh:=endpoint_triangle_row_load (Q:=endpointHostGraph R H A B) (F:=F) hST v hv (fun e=>weight e/d)
  change (∑ C : EndpointTriangle (endpointHostGraph R H A B) F
    (common A {x} (fun y=>R.neighborFinset y)) (common B {x} (fun y=>H.neighborFinset y)),
      if v∈C.val then weight (endpointTriangleRowEdge C)/d else 0)=_
  rw [hh]
  unfold endpointRowPotential
  apply Finset.sum_congr rfl
  intro p hp
  rw [endpoint_row_potential_predicate_present P R H F A B x v hAB hR hFB hv p]

theorem endpoint_index_potential_present (P R H F : SimpleGraph V) (A B : Finset V)
    (x u : V) (hAB : Disjoint A B) (hR : R≤P\F)
    (hFB : ∀ z∈B,∀ w,¬F.Adj z w)
    (hu : u∈common B {x} (fun y=>H.neighborFinset y)) (weight : Sym2 V→ℝ) (d : ℝ) :
    hypergraphWeightedDegree endpointTriangleVertices
      (fun C : EndpointTriangle (endpointHostGraph R H A B) F
        (common A {x} (fun y=>R.neighborFinset y)) (common B {x} (fun y=>H.neighborFinset y))=>
          weight (endpointTriangleRowEdge C)/d) u = endpointIndexPotential P R H F A x u weight d := by
  have hST : Disjoint (common A {x} (fun y=>R.neighborFinset y)) (common B {x} (fun y=>H.neighborFinset y)) :=
    hAB.mono (fun z hz=>((mem_singleton_common_graph R A x z).mp hz).1)
      (fun z hz=>((mem_singleton_common_graph H B x z).mp hz).1)
  have hh:=endpoint_triangle_index_load (Q:=endpointHostGraph R H A B) (F:=F) hST u hu (fun e=>weight e/d)
  change (∑ C : EndpointTriangle (endpointHostGraph R H A B) F
    (common A {x} (fun y=>R.neighborFinset y)) (common B {x} (fun y=>H.neighborFinset y)),
      if u∈C.val then weight (endpointTriangleRowEdge C)/d else 0)=_
  rw [hh]
  unfold endpointIndexPotential
  apply Finset.sum_congr rfl
  intro edge he
  rw [endpoint_index_potential_predicate_present P R H F A B x u hAB hR hFB hu edge]

theorem endpoint_triangle_parent_edge (P R H F : SimpleGraph V) (A B : Finset V) (x : V)
    (hAB : Disjoint A B) (hR : R≤P\F) (hFB : ∀ u∈B,∀ w,¬F.Adj u w)
    (C : EndpointTriangle (endpointHostGraph R H A B) F
      (common A {x} (fun y=>R.neighborFinset y)) (common B {x} (fun y=>H.neighborFinset y))) :
    endpointTriangleRowEdge C∈(endpointEligibleGraph P F (A∩P.neighborFinset x) x).edgeSet := by
  have hST : Disjoint (common A {x} (fun y=>R.neighborFinset y)) (common B {x} (fun y=>H.neighborFinset y)) :=
    hAB.mono (fun z hz=>((mem_singleton_common_graph R A x z).mp hz).1)
      (fun z hz=>((mem_singleton_common_graph H B x z).mp hz).1)
  let u:=endpointTriangleIndex C
  have hu:=endpointTriangleIndex_mem C
  obtain ⟨e,he⟩:=endpoint_triangle_index_coordinates_equiv hST u hu.2
  let D : {C' : EndpointTriangle (endpointHostGraph R H A B) F
      (common A {x} (fun y=>R.neighborFinset y)) (common B {x} (fun y=>H.neighborFinset y)) // u∈C'.val}:=⟨C,hu.1⟩
  have hh:=(e D).property
  rw [←he D] at hh
  exact ((endpoint_index_potential_predicate_present P R H F A B x u hAB hR hFB hu.2 _).mp hh).1

end Oberwolfach
