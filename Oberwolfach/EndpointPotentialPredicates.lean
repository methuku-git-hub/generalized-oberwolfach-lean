module

public import Oberwolfach.EndpointTriangleRowLoad
public import Oberwolfach.EndpointTriangleIndexLoad
public import Oberwolfach.EndpointMatchingMass
public import Oberwolfach.EndpointHostGraph

@[expose] public section

/-! The candidate conditions in the two source potential sums. The tested
root edge is omitted. The parent graph, conflict graph and eligible family
do not change with the realized rim/spoke subgraphs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

def EndpointRowPotentialPredicate (P R H F : SimpleGraph V) (A B : Finset V)
    (x v : V) (p : V×V) : Prop :=
  p.1∈B ∧ (endpointEligibleGraph P F (A∩P.neighborFinset x) x).Adj v p.2 ∧
    R.Adj x p.2 ∧ R.Adj v p.2 ∧ H.Adj x p.1 ∧ H.Adj v p.1 ∧ H.Adj p.2 p.1

def EndpointIndexPotentialPredicate (P R H F : SimpleGraph V) (A : Finset V)
    (x u : V) (edge : Sym2 V) : Prop :=
  edge∈(endpointEligibleGraph P F (A∩P.neighborFinset x) x).edgeSet ∧
    edge∈R.edgeSet ∧ ∀ v∈edge,R.Adj x v ∧ H.Adj v u

theorem mem_singleton_common_graph (G : SimpleGraph V) (A : Finset V) (x v : V) :
    v∈common A {x} (fun y=>G.neighborFinset y) ↔ v∈A ∧ G.Adj x v := by
  rw [mem_common_iff]
  simp only [Finset.mem_singleton,forall_eq,SimpleGraph.mem_neighborFinset]

theorem endpoint_row_potential_predicate_present (P R H F : SimpleGraph V) (A B : Finset V)
    (x v : V) (hAB : Disjoint A B) (hR : R≤P\F)
    (hFB : ∀ u∈B,∀ w,¬F.Adj u w)
    (hv : v∈common A {x} (fun y=>R.neighborFinset y)) (p : V×V) :
    EndpointRowPair (endpointHostGraph R H A B) F
      (common A {x} (fun y=>R.neighborFinset y)) (common B {x} (fun y=>H.neighborFinset y)) v p ↔
      EndpointRowPotentialPredicate P R H F A B x v p := by
  have hv' := (mem_singleton_common_graph R A x v).mp hv
  have hvPx : v∈A∩P.neighborFinset x:=Finset.mem_inter.mpr ⟨hv'.1,by simpa using (hR hv'.2).1⟩
  constructor
  · intro h
    have hu := (mem_singleton_common_graph H B x p.1).mp h.index_mem
    have hw := (mem_singleton_common_graph R A x p.2).mp h.other_mem
    have heR := (endpointHostGraph_row R H A B hAB hv'.1 hw.1).mp h.row_adj
    have heG:=hR heR
    have hwPx : p.2∈A∩P.neighborFinset x:=Finset.mem_inter.mpr ⟨hw.1,by simpa using (hR hw.2).1⟩
    exact ⟨hu.1,⟨hvPx,hwPx,(hR hv'.2).2,(hR hw.2).2,heG.1,heG.2⟩,
      hw.2,heR,hu.2,(endpointHostGraph_spoke R H A B hAB hv'.1 hu.1).mp h.first_spoke.symm,
      (endpointHostGraph_spoke R H A B hAB hw.1 hu.1).mp h.second_spoke.symm⟩
  · rintro ⟨huB,he,hwR,hvwR,hxu,hvu,hwu⟩
    have hwA : p.2∈A:=(Finset.mem_inter.mp he.2.1).1
    exact ⟨(mem_singleton_common_graph H B x p.1).mpr ⟨huB,hxu⟩,
      (mem_singleton_common_graph R A x p.2).mpr ⟨hwA,hwR⟩,hvwR.ne,
      (endpointHostGraph_row R H A B hAB hv'.1 hwA).mpr hvwR,
      ((endpointHostGraph_spoke R H A B hAB hv'.1 huB).mpr hvu).symm,
      ((endpointHostGraph_spoke R H A B hAB hwA huB).mpr hwu).symm,
      (hR hvwR).2,hFB p.1 huB v,hFB p.1 huB p.2⟩

theorem endpoint_index_potential_predicate_present (P R H F : SimpleGraph V) (A B : Finset V)
    (x u : V) (hAB : Disjoint A B) (hR : R≤P\F)
    (hFB : ∀ z∈B,∀ w,¬F.Adj z w)
    (hu : u∈common B {x} (fun y=>H.neighborFinset y)) (edge : Sym2 V) :
    EndpointIndexEdge (endpointHostGraph R H A B) F
      (common A {x} (fun y=>R.neighborFinset y)) u edge ↔
      EndpointIndexPotentialPredicate P R H F A x u edge := by
  have hu' := (mem_singleton_common_graph H B x u).mp hu
  induction edge using Sym2.ind with
  | _ v w =>
    constructor
    · intro h
      have hv := (mem_singleton_common_graph R A x v).mp (h.rows_mem v (by simp))
      have hw := (mem_singleton_common_graph R A x w).mp (h.rows_mem w (by simp))
      have hvwR := (endpointHostGraph_row R H A B hAB hv.1 hw.1).mp h.row_edge
      have hvPx : v∈A∩P.neighborFinset x:=Finset.mem_inter.mpr ⟨hv.1,by simpa using (hR hv.2).1⟩
      have hwPx : w∈A∩P.neighborFinset x:=Finset.mem_inter.mpr ⟨hw.1,by simpa using (hR hw.2).1⟩
      refine ⟨⟨hvPx,hwPx,(hR hv.2).2,(hR hw.2).2,(hR hvwR).1,(hR hvwR).2⟩,hvwR,?_⟩
      intro z hz
      rcases Sym2.mem_iff.mp hz with hzv|hzw
      · subst z
        exact ⟨hv.2,(endpointHostGraph_spoke R H A B hAB hv.1 hu'.1).mp (h.spokes v (by simp)).symm⟩
      · subst z
        exact ⟨hw.2,(endpointHostGraph_spoke R H A B hAB hw.1 hu'.1).mp (h.spokes w (by simp)).symm⟩
    · rintro ⟨he,hvw,hn⟩
      have hvwR : R.Adj v w:=hvw
      have hvA : v∈A:=(Finset.mem_inter.mp he.1).1
      have hwA : w∈A:=(Finset.mem_inter.mp he.2.1).1
      refine ⟨?_,(endpointHostGraph_row R H A B hAB hvA hwA).mpr hvwR,(hR hvwR).2,?_,?_⟩
      · intro z hz
        have hzA : z∈A := by rcases Sym2.mem_iff.mp hz with rfl|rfl;exact hvA;exact hwA
        exact (mem_singleton_common_graph R A x z).mpr ⟨hzA,(hn z hz).1⟩
      · intro z hz
        have hzA : z∈A := by rcases Sym2.mem_iff.mp hz with rfl|rfl;exact hvA;exact hwA
        exact ((endpointHostGraph_spoke R H A B hAB hzA hu'.1).mpr (hn z hz).2).symm
      · intro z hz;exact hFB u hu'.1 z

end Oberwolfach
