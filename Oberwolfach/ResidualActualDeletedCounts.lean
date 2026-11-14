module

public import Oberwolfach.ResidualTwoFactorEdgeCount
public import Oberwolfach.ResidualDisjointPathCount
public import Oberwolfach.ResidualDisjointCycleCount

@[expose] public section
/-! Exact residual counts for vertex-disjoint deleted cycles and paths in
an actual two-factor. The path endpoints remain in the residual vertex set. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V I J:Type} [Fintype V] [DecidableEq V] [DecidableEq I] [DecidableEq J]

theorem two_factor_residual_count_after_disjoint_deletions
    (F:SimpleGraph V) (hF:F.IsRegularOfDegree 2)
    (s:Finset I) (u v:I→V) (P:∀ i,F.Walk (u i) (v i))
    (hp:∀i∈s,(P i).IsPath) (hne:∀i∈s,u i≠v i)
    (hP:(↑s:Set I).PairwiseDisjoint (fun i=>(P i).support.toFinset))
    (t:Finset J) (root:J→V) (C:∀ j,F.Walk (root j) (root j))
    (hc:∀j∈t,(C j).IsCycle)
    (hC:(↑t:Set J).PairwiseDisjoint (fun j=>(C j).support.toFinset))
    (hcross:∀i∈s,∀j∈t,Disjoint (P i).support.toFinset (C j).support.toFinset):
    let deletedV := (t.biUnion (fun j=>(C j).support.toFinset)) ∪
      (s.biUnion (fun i=>(P i).support.toFinset \ {u i,v i}))
    let deletedE := (t.biUnion (fun j=>(C j).edges.toFinset)) ∪
      (s.biUnion (fun i=>(P i).edges.toFinset));
    (F.edgeFinset \ deletedE).card + s.card = (Finset.univ \ deletedV).card := by
  let CV := t.biUnion (fun j=>(C j).support.toFinset)
  let CE := t.biUnion (fun j=>(C j).edges.toFinset)
  let PV := s.biUnion (fun i=>(P i).support.toFinset \ {u i,v i})
  let PE := s.biUnion (fun i=>(P i).edges.toFinset)
  have hcvpe : Disjoint CV PV := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨j,hj,hx⟩:=Finset.mem_biUnion.mp hx
    obtain ⟨i,hi,hy⟩:=Finset.mem_biUnion.mp hy
    exact Finset.disjoint_left.mp (hcross i hi j hj) (Finset.mem_sdiff.mp hy).1 hx
  have hcepe : Disjoint CE PE := by
    apply Finset.disjoint_left.mpr
    intro e hx hy
    obtain ⟨j,hj,hx⟩:=Finset.mem_biUnion.mp hx
    obtain ⟨i,hi,hy⟩:=Finset.mem_biUnion.mp hy
    induction e using Sym2.ind with
    | _ x y =>
      have hx' : x∈(C j).support.toFinset := by
        apply List.mem_toFinset.mpr
        exact (C j).fst_mem_support_of_mem_edges (List.mem_toFinset.mp hx)
      have hy' : x∈(P i).support.toFinset := by
        apply List.mem_toFinset.mpr
        exact (P i).fst_mem_support_of_mem_edges (List.mem_toFinset.mp hy)
      exact Finset.disjoint_left.mp (hcross i hi j hj) hy' hx'
  have hEsub : CE∪PE⊆F.edgeFinset := by
    intro e he
    rcases Finset.mem_union.mp he with he|he
    · obtain ⟨j,hj,hj'⟩:=Finset.mem_biUnion.mp he
      exact SimpleGraph.mem_edgeFinset.mpr ((C j).edges_subset_edgeSet (List.mem_toFinset.mp hj'))
    · obtain ⟨i,hi,hi'⟩:=Finset.mem_biUnion.mp he
      exact SimpleGraph.mem_edgeFinset.mpr ((P i).edges_subset_edgeSet (List.mem_toFinset.mp hi'))
  have hVsub:CV∪PV⊆(Finset.univ:Finset V) := Finset.subset_univ _
  have hEc := Finset.card_sdiff_add_card_eq_card hEsub
  have hVc := Finset.card_sdiff_add_card_eq_card hVsub
  have hCE:CE.card=CV.card:=disjoint_cycle_walks_edge_vertex_count F t root C hc hC
  have hPE:PE.card=PV.card+s.card:=disjoint_simple_paths_edges_and_internal_vertices F s u v P hp hne hP
  have hEunion:(CE∪PE).card=CE.card+PE.card:=Finset.card_union_of_disjoint hcepe
  have hVunion:(CV∪PV).card=CV.card+PV.card:=Finset.card_union_of_disjoint hcvpe
  have hFcard:=two_factor_edge_count F hF
  change (F.edgeFinset \ (CE∪PE)).card+s.card = ((Finset.univ:Finset V) \ (CV∪PV)).card
  rw [hEunion,hCE,hPE,hFcard] at hEc
  rw [hVunion,Finset.card_univ] at hVc
  omega
end Oberwolfach
